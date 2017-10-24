module HashMap
open System.Collections.Generic
open System


type Buffer8<'T>() =
    let [<Literal>] ShardSize = 8
    let buffer = ResizeArray<'T []>(32)
    let locks = ResizeArray<obj>(32)
    let rental = ResizeArray<int>(32)
    let mutable freeList : int list = []
    let empty = Array.zeroCreate<'T>(ShardSize)
    //let mutable freeListCount = 0

    member __.Empty() = (-1,empty)

    member __.Empty(index:int,rindex:int [],bucket: 'T [] []) =
        rindex.[index] <- -1
        bucket.[index] <- empty

    member __.Rent() =
        match freeList with
        | [] ->
            let newBuffer = Array.zeroCreate<'T>(ShardSize) 
            let index = buffer.Count
            buffer.Add newBuffer
            rental.Add 1
            (index,newBuffer)
        | h :: t -> 
            freeList <- t
            rental.[h] <- 1
            (h,buffer.[h])

    member x.Rent(bindex:int,rindex:int [],bucket: 'T [] []) =
        let ri,s = x.Rent()
        rindex.[bindex] <- ri
        bucket.[bindex] <- s
        s

    member __.Return(index:int,ary: 'T []) =
        if index <> - 1 then
            match rental.[index] with
            | 0 -> failwith "A buffer as been returned when with rentals already zero"
            | 1 ->    
                Array.Clear(ary,0,ShardSize)
                rental.[index] <- 0
                freeList <- index :: freeList
            | x ->
                rental.[index] <- x - 1
    
    /// creates new shard at index with shallow copy of old references
    member x.CopyNew(bindex:int,rindex:int [],bucket: 'T [] []) =
        let oshard = bucket.[bindex] 
        let nri,nshrd = x.Rent()
        Array.Copy(oshard,nshrd,ShardSize)
        x.Return(rindex.[bindex],oshard)
        rindex.[bindex] <- nri
        bucket.[bindex] <- nshrd
        nshrd

    member __.Exclusive(index:int) =
        rental.[index] = 1

module Buffer8Factory =
    let private buffers = Dictionary<System.Type,obj>()
    let GetBuffer8<'T>() =
        let t = typeof<'T>
        match buffers.TryGetValue t with
        | true, v -> v :?> Buffer8<'T> 
        | false,_ ->
            let newBuf = Buffer8<'T>()
            buffers.Add(t, newBuf)
            newBuf

// Helper Functions
////////////////////////////


let private calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))
let inline private pow2 (i:int) = 2 <<< (i - 1)
let inline private isEmpty v = Object.ReferenceEquals(null,v)

type ShardMap<'K,'V  when 'K :> IEqualityComparer<'K> and 'K : comparison>(nRIndex:int [],nBucket: Map<'K,'V> [] []) =
    
    let [<Literal>] InitialSize = 2 // 2 * 8 = 16 
    let buffer = Buffer8Factory.GetBuffer8<Map<'K,'V>>()
    let mutable rindex = nRIndex //Array.zeroCreate<int> InitialSize
    let mutable bucket = nBucket 
        // Array.init InitialSize (fun i -> 
        //     let ri,shrd = buffer.Empty()
        //     rindex.[i] <- ri
        //     shrd
        // )
    //Lock variables
    let mutable resizing = false
    let resizeLock = obj

    let mutable count = 0 

    //let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))

    let mutable bitMaskDepth = 0
    
    let calcpBitMask (bitDepth:int) = ~~~(-1 <<< (bitDepth))
    let mutable pBitMask = calcpBitMask bitMaskDepth
    ///provides index in local bucket of shard
    let bucketIndex (keyHash:int,bitdepth:int) = (keyHash &&& (~~~(-1 <<< (bitdepth)))) >>> 3// todo: improve substring bitmask calc
    
    ///provides sub index in shards
    let shardIndex (keyHash:int) = keyHash &&& 0b111

    let higherRange (index:int,bitdepth:int) = (index ||| 1 <<< bitdepth) >>> 3  

    let item (key:'K) =
        let kh = key.GetHashCode()
        let m = bucket.[bucketIndex(kh,bucket.Length)].[shardIndex kh]
        if isEmpty m then
            raise <| KeyNotFoundException(sprintf "Key:%A , does not exist in the dictionary" key)
        else
            m.Item key

    member __.Add(k:'K,v:'V) =
        if count + 1 > (bucket.Length * 8) then
            // base array needs resizing
            resizing <- true
            lock resizeLock (fun () ->

                let isize = bucket.Length
                let ibmd = calcBitMaskDepth isize
                let nbmd = ibmd + 1
                let newBucket = Array.zeroCreate<Map<'K,'V> []> (isize * 2)
                let newRIndex = Array.zeroCreate<int> (isize * 2)
                for i in 0 .. isize - 1 do
                    let shrd = bucket.[i]
                    let i2 = (i ||| 1 <<< ibmd) >>> 3 
                    if rindex.[i] = -1 then // special empty case
                        buffer.Empty(i,newRIndex,newBucket)
                        buffer.Empty(i2,newRIndex,newBucket)
                    else // shard needs to be split out amoungst two new shards

                        //skip (or impliment with adding empty arrays)
                        // let ri0, s0 = buffer.Rent()
                        // newRIndex.[i] <- ri0

                        for j in 0 .. 7 do
                            let m = shrd.[j]
                            if not (isEmpty m) then
                                let m1,m0 = Map.partition (fun k _ -> (k.GetHashCode() >>> ibmd) &&& 0b1 = 1) m
                                
                                if not m0.IsEmpty then
                                    let mutable shrd = newBucket.[i]
                                    if isEmpty shrd then
                                        shrd <- buffer.Rent(i,newRIndex,newBucket)
                                    shrd.[j] <- m0
                                
                                if not m1.IsEmpty then
                                    let mutable  shrd = newBucket.[i2]
                                    if isEmpty shrd then
                                        shrd <- buffer.Rent(i2,newRIndex,newBucket)
                                    shrd.[j] <- m1

                        // after copying, check if buckets still empty and add empty shard if null
                        if isEmpty newBucket.[i] then buffer.Empty(i,newRIndex,newBucket)
                        if isEmpty newBucket.[i2] then buffer.Empty(i2,newRIndex,newBucket)
                    
                    buffer.Return(rindex.[i],bucket.[i])
                //now update internal state
                bucket <- newBucket
                rindex <- newRIndex
                    
            ) //End of Lock
            resizing <- false
        
        /// Resize complete at this stage if needed
        let kh = k.GetHashCode()
        let bi = bucketIndex(kh,bucket.Length)
        let si = shardIndex kh
        let shrd =
            if buffer.Exclusive(rindex.[bi]) then
                bucket.[bi]     // If only one renting buffer, can mutate 
            else
                buffer.CopyNew(bi,rindex,bucket) // if copied by others, then new buffer needed 
        let m = shrd.[si]
        if isEmpty m then
            shrd.[si] <- Map<'K,'V>([(k,v)])
        else
            shrd.[si] <- m.Add(k,v)

    member __.Copy() =
        let nRIndex = Array.zeroCreate<int>(rindex.Length)
        Array.Copy(rindex,nRIndex,rindex.Length)
        
        let nBucket = Array.zeroCreate<Map<'K,'V>[]>(nBucket.Length)
        Array.Copy(bucket,nBucket,bucket.Length)

        ShardMap<'K,'V>(nRIndex,nBucket)
                

    member __.Item(key:'K) =
        if resizing then
            lock resizeLock (fun () -> item key)
        else
            item key

    new(kvps:('K * 'V) seq) =
        let mutable counter = 0
        let mutable items = []
        for kvp in kvps do
            counter <- counter + 1
            items <- kvp :: items
        let bd = calcBitMaskDepth counter
        let bucketSize = pow2 bd
        
        
        ShardMap<'K,'V>()
        


open System
let printer (i:int) = Convert.ToString(i, 2)
let bitTest (keyHash:int) (arySize) = ~~~(-1 <<< (arySize ))  //|> printer
bitTest 8582851 6
(63 &&& 2568749) >>> 3 |> printer
bitMask 9103477 6
let ma = Array.zeroCreate<Map<string,int>>(3)
ma.[1] <- Map.empty
if Object.ReferenceEquals(null,ma.[1]) then None else Some ma.[1]
2 <<< 5
47