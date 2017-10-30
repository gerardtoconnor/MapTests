module HashMap

open MapOld
open SampleData
#time

open System.Collections.Generic
open System
open NonStructuralComparison



[<Literal>] 
let private ShardSize = 16
//let private empty = Array.zeroCreate<Map<'K,'V>>(ShardSize)

// Helper Functions
////////////////////////////

//let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2))) //todo:make private
let inline calcBitMaskDepth i =
    let rec go s d =
        if s = 0 then d
        else go (s >>> 1) (d + 1)
    go i 0
let inline private pow2 (i:int) = 2 <<< (i - 5) // todo 4 is shard size 2^n
let inline calcSubBitMask (bitDepth:int) = ~~~(-1 <<< (bitDepth))

///prvides index in bucket of shard
let inline private bucketIndex (keyHash:int,subBitMask:int) = (keyHash &&& subBitMask) >>> 4// todo: improve substring bitmask calc

let inline private bucketIndexOld (keyHash:int,bitdepth:int) = (keyHash &&& (~~~(-1 <<< (bitdepth)))) >>> 4// todo: improve substring bitmask calc

///provides sub index in shards
let inline private shardIndex (keyHash:int) = keyHash &&& 0b1111
let inline private isEmpty v = Object.ReferenceEquals(null,v)

/// Shard Map Ittr
////////////////////////////

type ShardMapIterator<'K,'V when 'K : comparison>(bucket:SubMap<'K,'V> [] []) =
    let mutable mapEnum = Unchecked.defaultof<IEnumerator<KeyValuePair<'K,'V>>>
    let mutable bi = 0
    let mutable si = 0
    let mutable started = false
    
    let mutable skipped = 0
    let mutable found = 0
    
    // let rec nextMap () =

    //     let testMap () = 
    //         let m = bucket.[bi].[si]
    //         if isEmpty m then
    //             skipped <- skipped + 1 
    //             nextMap ()
    //         else
    //             found <- found + 1
    //             mapEnum <- (m :> IEnumerable<_>).GetEnumerator()
    //             if mapEnum.MoveNext() then
    //                 true
    //             else
    //                 nextMap ()    

    //     if si + 1 < ShardSize then
    //         si <- si + 1
    //         testMap ()           
    //     else
    //         if bi + 1 < bucket.Length then
    //             bi <- bi + 1
    //             si <- 0
    //             testMap ()
    //         else
    //             //printfn "itterator disposed with %i found and %i skipped" found skipped
    //             false

    // member __.Current = mapEnum.Current
    // member __.MoveNext() = 
    //     if started then
    //         if mapEnum.MoveNext() then 
    //             true
    //         else
    //             nextMap ()
    //     else
    //         started <- true
    //         let m = bucket.[0].[0]
    //         if isEmpty m then
    //             skipped <- skipped + 1 
    //             nextMap ()
    //         else
    //             found <- found + 1
    //             mapEnum <- (m :> IEnumerable<_>).GetEnumerator()
    //             if mapEnum.MoveNext() then
    //                 true
    //             else
    //                 nextMap () 
    // member __.Reset() =
    //     bi <- 0
    //     si <- 0
    //     started <- false

    // member __.Dispose() = ()



/// Shard Map
////////////////////////////

type ShardMap<'K,'V  when 'K : equality and 'K : comparison>(icount:int, nBucket:SubMap<'K,'V> [] [], ihead:SubMap<'K,'V>) =

    let empty = Array.zeroCreate<SubMap<'K,'V>>(ShardSize)

    let mutable subMapHead = ihead

    let genNewSubMap kvt =
        let sm = SubMap<_,_>.FromOne kvt subMapHead
        subMapHead <- sm
        sm

    let newShard oary = 
        let nary = Array.zeroCreate<SubMap<'K,'V>>(ShardSize)
        Array.Copy(oary,nary,ShardSize)
        nary

    let mutable bucket = nBucket 
        // Array.init InitialSize (fun i -> 
        //     let ri,shrd = buffer.Empty()
        //     rindex.[i] <- ri
        //     shrd
        // )
    //Lock variables
    let mutable resizing = false
    let resizeLock = obj

    let mutable count = icount 

    //let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))

    let mutable bitMaskDepth = calcBitMaskDepth icount
    
    let mutable bucketBitMask = calcSubBitMask bitMaskDepth
    ///provides index in local bucket of shard


    let higherRange (index:int,bitdepth:int) = (index ||| 1 <<< bitdepth) >>> 4 

    let item (key:'K) =
        let kh = key.GetHashCode()
        let m = bucket.[bucketIndex(kh,bucketBitMask)].[shardIndex kh]
        if isEmpty m then
            raise <| KeyNotFoundException(sprintf "Key:%A , does not exist in the dictionary" key)
        else
            m.Item key

    do  // prevent any out of index errors on non-set shards
        for bi in 0.. bucket.Length - 1 do
        if isEmpty bucket.[bi] then
            bucket.[bi] <- empty

    member __.Add(k:'K,v:'V) =
        if count + 1 > (bucket.Length * ShardSize) then
            // base array needs resizing
            resizing <- true
            lock resizeLock (fun () ->

                let isize = bucket.Length
                let ibmd = calcBitMaskDepth isize
                let newBucket = Array.zeroCreate<SubMap<'K,'V> []> (isize * 2)
                let newRIndex = Array.zeroCreate<int> (isize * 2) // <<< todo: change to create -1s so rindex can be checked processing and at end
                for i in 0 .. isize - 1 do
                    let shrd = bucket.[i]
                    let i2 = (i ||| 1 <<< ibmd) >>> 4
                    if Object.ReferenceEquals(empty,bucket.[i]) then // special empty case
                        newBucket.[i] <- empty
                        newBucket.[i2] <- empty
                    else // shard needs to be split out amoungst two new shards

                        //skip (or impliment with adding empty arrays)
                        // let ri0, s0 = buffer.Rent()
                        // newRIndex.[i] <- ri0

                        for j in 0 .. 7 do
                            let m = shrd.[j]
                            if not (isEmpty m) then
                                let m1,m0 = m.Partition (fun k _ -> (k.GetHashCode() >>> ibmd) &&& 0b1 = 1)
                                
                                if not m0.IsEmpty then
                                    let mutable shrd = newBucket.[i]
                                    if isEmpty shrd then
                                        shrd <- Array.zeroCreate<_>(ShardSize)
                                        newBucket.[i] <- shrd
                                    shrd.[j] <- m0
                                
                                if not m1.IsEmpty then
                                    let mutable  shrd = newBucket.[i2]
                                    if isEmpty shrd then
                                        shrd <- Array.zeroCreate<_>(ShardSize)
                                        newBucket.[i2] <- shrd
                                    shrd.[j] <- m1

                        // after copying, check if buckets still empty and add empty shard if null
                        if isEmpty newBucket.[i] then newBucket.[i] <- empty
                        if isEmpty newBucket.[i2] then newBucket.[i2] <- empty
                    
                //now update internal state
                bucket <- newBucket  /// <<<<<<<<<<<<<<< NOT ANYMORE MUTATE TO NEW DICT
                    
            ) //End of Lock
            resizing <- false
        
        /// Resize complete at this stage if needed
        let kh = k.GetHashCode()
        let bi = bucketIndex(kh,bucketBitMask)
        let si = shardIndex kh
        let shrd = newShard bucket.[bi]
        bucket.[bi] <- shrd
        let m = shrd.[si]
        if isEmpty m then
            shrd.[si] <- genNewSubMap (k,v)
        else
            shrd.[si] <- m.Add(k,v)

    member __.Remove(k:'K) =
        let kh = k.GetHashCode()
        let bi = bucketIndex(kh,bucketBitMask)
        let si = shardIndex kh
        let shrd = newShard bucket.[bi]
        bucket.[bi] <- shrd
        let m = shrd.[si]
        if isEmpty m then
            raise <| KeyNotFoundException(sprintf "Key:'%A' not found in map so cannot remove" k)
        else
            shrd.[si] <- m.Remove(k)

    member __.Copy() =        
        let nBucket = Array.zeroCreate<SubMap<'K,'V>[]>(nBucket.Length)
        Array.Copy(bucket,nBucket,bucket.Length)
        ShardMap<'K,'V>(count,nBucket,subMapHead)
                
    member x.AddToNew(k:'K,v:'V) =
        let newShardMap = x.Copy()
        newShardMap.Add(k,v)
        newShardMap

    member x.RemoveToNew(k:'K) =
        let newShardMap = x.Copy()
        newShardMap.Remove(k)
        newShardMap
        
    member __.Item(key:'K) =
        if resizing then
            lock resizeLock (fun () -> item key)
        else
            item key

    member __.ContainsKey(key:'K) =
        let kh = key.GetHashCode()
        let m = bucket.[bucketIndex(kh,bucketBitMask)].[shardIndex kh]
        //printfn "?| looking for key:'%A' [%i][%i] in map{%A}" key bi si m
        if isEmpty m then
            false
        else
            m.ContainsKey key

    // member __.toSeqSlow () = seq {
    //         for i in 0 .. bucket.Length - 1 do
    //             for j in 0 .. ShardSize - 1 do
    //                 let m = bucket.[i].[j]
    //                 if not(isEmpty m) then
    //                     for kvp in m -> kvp
    //     }

    // member __.toSeq () = 
    //     let i = ref (ShardMapIterator(bucket))
    //     { new IEnumerator<_> with 
    //               member self.Current = (!i).Current
    //           interface System.Collections.IEnumerator with
    //               member self.Current = box (!i).Current
    //               member self.MoveNext() = (!i).MoveNext()
    //               member self.Reset() = i :=  ShardMapIterator(bucket)
    //           interface System.IDisposable with 
    //               member self.Dispose() = ()}


    member __.Count with get () = count

    member __.BucketSize with get () = bucket.Length

    member __.PrintLayout () =
        let mutable rowCount = 0
        let mutable tmapCount = 0
        let mutable rmapCount = 0
        let columnCount = Array.zeroCreate<int>(bucket.Length)
        printfn "Printing Layout:"
        for i in 0 .. bucket.Length - 1 do
            rowCount <- 0
            rmapCount <- 0

            printf "%3i {" i
            for j in 0 .. ShardSize - 1 do
                let m = bucket.[i].[j]
                if isEmpty m then
                    printf " __ |"
                else
                    tmapCount <- tmapCount + 1
                    rmapCount <- rmapCount + 1
                    columnCount.[i] <- columnCount.[i] + m.Count
                    rowCount <- rowCount + m.Count
                    printf " %2i |" m.Count
            printfn "} = %4i[%5i]"rmapCount rowCount
        
        printf "Tot {" 
        for j in 0 .. ShardSize - 1 do
            printf " %i |" columnCount.[j]
        printfn "} = %4i[%5i]" tmapCount count            
    
    member __.SubMapList () =
        let rec go (sm:SubMap<_,_>) acc =
            if isEmpty sm then
                acc
            else
                go sm.Tail (sm :: acc) 
        go subMapHead []


    interface IEnumerable<KeyValuePair<'K, 'V>> with
        member s.GetEnumerator() = subMapHead.ToSeq()

    interface System.Collections.IEnumerable with
        override s.GetEnumerator() = (subMapHead.ToSeq() :> System.Collections.IEnumerator)

        
    new(counter:int,items:('K * 'V) seq) =

        let bitdepth = calcBitMaskDepth counter
        let bucketSize = pow2 bitdepth
        let bucketBitMask = calcSubBitMask bitdepth
        let newBucket = Array.zeroCreate<SubMap<'K,'V> []>(bucketSize)
        let mutable mapHead = Unchecked.defaultof<SubMap<_,_>>

        items
        |> Seq.iter (fun (k,v) -> 
                let kh = k.GetHashCode()
                let bi = bucketIndex(kh,bucketBitMask)
                let mutable shrd = newBucket.[bi]
                if isEmpty shrd then
                    shrd <- Array.zeroCreate<_>(ShardSize)
                    newBucket.[bi] <- shrd
                let si = shardIndex(kh)
                let m = shrd.[si]
                shrd.[si] <- 
                    if isEmpty m then
                        //printfn "$| creating new map for key:'%A' [%i][%i] for value:%A" k bi si v
                        let m2 = SubMap<_,_>.FromOne (k,v) mapHead
                        mapHead <- m2
                        m2
                    else
                        //printfn "+| adding key:'%A' [%i][%i] for value:%A to map {%A}" k bi si v m
                        m.Add(k,v)                        
            )
        //now allocate any empties that were not filled
        
        ShardMap<'K,'V>(counter,newBucket,mapHead)

    new(kvps:('K * 'V) seq) =       
        let mutable counter = 0
        let mutable items = []
        kvps |> Seq.iter (fun kvp -> 
            counter <- counter + 1
            items <- kvp :: items
        )
        ShardMap<_,_>(counter,items)

    new(kvps:('K * 'V) []) =      
        ShardMap<_,_>(kvps.Length,kvps)
        

///////////////////////////////////////////////
///////////////////////////////////////////////
// The END
///////////////////////////////////////////////
///////////////////////////////////////////////

let emptySM = Unchecked.defaultof<SubMap<string,string>>
let smt = SubMap<_,_>.FromOne ("jhlkh","poinkjh") emptySM
smt.Tail
printfn "%A" smt

let smt1 = smt.Add("poijoihj","vyrctoiuou")  
printfn "%A" smt1
smt.Tail
let smt2 = SubMap<_,_>.FromOne ("dsdfdlkh","poinsfvdsf") smt1
smt2.Tail
let smt3 = smt2.Add("asfaposdiufad","ghadfjfksaldjf")
smt3.Tail
for v in smt3 do
    printfn "%A" v
Object.ReferenceEquals(smt1,smt2.Tail)

let smap = new ShardMap<_,_>(numberStrings)
smap1.GetHashCode()
let smap1 = smap.AddToNew("alkdfjas","fadfdf")
let bmap = Map<_,_>(numberStrings)

smap.BucketSize
smap.Count
smap.PrintLayout()
let sml = smap.SubMapList()
calcBitMaskDepth smap.Count
List.length sml

2 <<< (11-5)

let dict = Dictionary<string,string>()
for (k,v) in numberStrings do
    dict.Add(k,v)

//////////////
for i in 0 .. 10000 do
    let bmap = Map<_,_>(numberStrings)
    ()

for i in 0 .. 10000 do
    let smap = new ShardMap<_,_>(numberStrings)
    ()

///////////////
let lookuploops = 10000

for i in 0 .. lookuploops do
    for (k,v) in numberStrings do
        if smap.[k] <> v then printfn "ERROR ON KEY MATCH: %A" k

for i in 0 .. lookuploops do
    for (k,v) in numberStrings do
        if dict.[k] <> v then
            printfn "ERROR ON KEY MATCH: %A" k

for i in 0 .. lookuploops do
    for (k,v) in numberStrings do
        if bmap.[k] <> v then printfn "ERROR ON KEY MATCH: %A" k
        
////////////
let copyloops = 100000
for i in 0 .. copyloops do
    let ndict = Dictionary<_,_>(dict)
    let k,v = "Key1","Value1" 
    ndict.Add(k,v)
    if not(ndict.ContainsKey(k)) || dict.ContainsKey(k) then failwith "Immutablity Error"


for i in 0 .. copyloops do
    let k,v = "Key1","Value1" 
    let ndict = smap.AddToNew(k,v)
    //ndict.Add(k,v)
    if not(ndict.ContainsKey(k)) then failwith "new dict does not contain added value"
    if smap.ContainsKey(k) then failwith "old dict has newly added value"

// for i in 0 .. copyloops do
//     let k,v = "Key1","Value1" 
//     smap.Add(k,v)
//     //ndict.Add(k,v)
//     if not(smap.ContainsKey(k)) then failwith "failed to addadded value"

for i in 0 .. copyloops do
    let k,v = "Key1","Value1"
    let ndict = bmap.Add(k,v)
    if not(ndict.ContainsKey(k)) then failwith "new dict does not contain added value"
    if bmap.ContainsKey(k) then failwith "old dict has newly added value"

///////////
let ittrLoops = 10000

let mutable counter = 0
printfn "coutner:%i" counter

for i in 0 .. ittrLoops do
    smap |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        counter <- counter + 1
        ()
    )

for i in 0 .. ittrLoops do
    bmap |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        counter <- counter + 1
        ()
    ) 

for i in 0 .. ittrLoops do
    dict |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        //counter <- counter + 1
        ()
    )

let ls = numberStrings |> Array.map (fun (k,v) -> KeyValuePair<_,_>(k,v) ) |> Array.toList
for i in 0 .. ittrLoops do
    ls |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        //counter <- counter + 1
        ()
    )
Seq.length smap

    smap |> Seq.iter (fun kvp ->
        printfn "'%A':'%A'" kvp.Key kvp.Value
    )

let bmap = bmap.Remove("Key1")

dict.Count   

smap.["Elekta"];;


#time
