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

    member x.Rent(index:int,rindex:int [],bucket: 'T [] []) =
        let ri,s = x.Rent()
        rindex.[index] <- ri
        bucket.[index] <- s

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

let inline private isEmpty v = Object.ReferenceEquals(null,v)

type ShardMap<'K,'V  when 'K :> IEqualityComparer<'K> and 'K : comparison>() =
    
    let [<Literal>] InitialSize = 2 // 2 * 8 = 16 
    let mutable buffer = Buffer8Factory.GetBuffer8<Map<'K,'V>>()
    let mutable rindex = Array.zeroCreate<int> InitialSize
    let bucket = Array.init InitialSize (fun i -> 
            let ri,shrd = buffer.Empty()
            rindex.[i] <- ri
            shrd
        )
    //Lock variables
    let mutable resizing = false
    let resizeLock = obj

    let mutable count = 0 

    let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))

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
                    else
                        //skip (or impliment with adding empty arrays)
                        let ri0, s0 = buffer.Rent()
                        newRIndex.[i] <- ri0

                        for j in 0 .. 7 do
                            let m = shrd.[j]
                            if not (isEmpty m) then
                                let m1,m0 = Map.partition (fun k _ -> (k.GetHashCode() >>> ibmd) &&& 0b1 = 1) m
                                if m0.IsEmpty then
                                    ()
                                else                            
                                    let shrd = newBucket.[i]
                                    if isEmpty shrd then
                                        let ri, s = buffer.Rent()
                                        newRIndex.[i] <- ri ; newBucket.[i] <- s
            ) //End of Lock
            resizing <- false
                
        else
            ()

    member __.Item(key:'K) =
        if resizing then
            lock resizeLock (fun () -> item key)
        else
            item key

open System
let printer (i:int) = Convert.ToString(i, 2)
let bitTest (keyHash:int) (arySize) = ~~~(-1 <<< (arySize ))  //|> printer
bitTest 8582851 6
(63 &&& 2568749) >>> 3 |> printer
bitMask 9103477 6
let ma = Array.zeroCreate<Map<string,int>>(3)
ma.[1] <- Map.empty
if Object.ReferenceEquals(null,ma.[1]) then None else Some ma.[1]
