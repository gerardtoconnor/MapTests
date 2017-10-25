module HashMap
open System.Collections.Generic
open System

[<Literal>] 
let private ShardSize = 8
//let private empty = Array.zeroCreate<Map<'K,'V>>(ShardSize)

// Helper Functions
////////////////////////////

let private calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))
let inline private pow2 (i:int) = 2 <<< (i - 1)

let inline calcSubBitMask (bitDepth:int) = ~~~(-1 <<< (bitDepth))

///prvides index in bucket of shard
let inline private bucketIndex (keyHash:int,subBitMask:int) = (keyHash &&& subBitMask) >>> 3// todo: improve substring bitmask calc

let inline private bucketIndexOld (keyHash:int,bitdepth:int) = (keyHash &&& (~~~(-1 <<< (bitdepth)))) >>> 3// todo: improve substring bitmask calc

///provides sub index in shards
let inline private shardIndex (keyHash:int) = keyHash &&& 0b111
let inline private isEmpty v = Object.ReferenceEquals(null,v)

type ShardMap<'K,'V  when 'K : equality and 'K : comparison>(icount:int, nBucket: Map<'K,'V> [] []) =

    let empty = Array.zeroCreate<Map<'K,'V>>(ShardSize)

    let newShard oary = 
        let nary = Array.zeroCreate<Map<'K,'V>>(ShardSize)
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


    let higherRange (index:int,bitdepth:int) = (index ||| 1 <<< bitdepth) >>> 3  

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
                let newBucket = Array.zeroCreate<Map<'K,'V> []> (isize * 2)
                let newRIndex = Array.zeroCreate<int> (isize * 2) // <<< todo: change to create -1s so rindex can be checked processing and at end
                for i in 0 .. isize - 1 do
                    let shrd = bucket.[i]
                    let i2 = (i ||| 1 <<< ibmd) >>> 3 
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
                                let m1,m0 = Map.partition (fun k _ -> (k.GetHashCode() >>> ibmd) &&& 0b1 = 1) m
                                
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
            shrd.[si] <- Map<'K,'V>([(k,v)])
        else
            shrd.[si] <- m.Add(k,v)

    member __.AddToNew(k:'K,v:'V) =
        /// Resize complete at this stage if needed
        let newBucket = Array.zeroCreate<Map<'K,'V>[]>(bucket.Length)
        Array.Copy(bucket,newBucket,bucket.Length)
        let newShardMap = ShardMap<_,_>(count,newBucket)
        newShardMap.Add(k,v)
        newShardMap
        
    member __.Copy() =        
        let nBucket = Array.zeroCreate<Map<'K,'V>[]>(nBucket.Length)
        Array.Copy(bucket,nBucket,bucket.Length)
        ShardMap<'K,'V>(count,nBucket)
                
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
        
    new(counter:int,items:('K * 'V) seq) =

        let bitdepth = calcBitMaskDepth counter
        let bucketSize = pow2 bitdepth
        let bucketBitMask = calcSubBitMask bitdepth
        let newBucket = Array.zeroCreate<Map<'K,'V> []>(bucketSize)
        
        items
        |> Seq.iter (fun (k,v) -> 
                let kh = k.GetHashCode()
                let bi = bucketIndex(kh,bucketBitMask)
                let mutable shrd = newBucket.[bi]
                if isEmpty shrd then
                    shrd <- Array.zeroCreate<_>(8)
                    newBucket.[bi] <- shrd
                let si = shardIndex(kh)
                let m = shrd.[si]
                shrd.[si] <- 
                    if isEmpty m then
                        //printfn "$| creating new map for key:'%A' [%i][%i] for value:%A" k bi si v
                        Map<'K,'V>([(k,v)])
                    else
                        //printfn "+| adding key:'%A' [%i][%i] for value:%A to map {%A}" k bi si v m
                        m.Add(k,v)                
            )
        //now allocate any empties that were not filled
        
        ShardMap<'K,'V>(counter,newBucket)

    new(kvps:('K * 'V) seq) =       
        let mutable counter = 0
        let mutable items = []
        kvps |> Seq.iter (fun kvp -> 
            counter <- counter + 1
            items <- kvp :: items
        )
        ShardMap<_,_>(counter,items)
        


///////////////////////////////////////////////
///////////////////////////////////////////////
// The END
///////////////////////////////////////////////
///////////////////////////////////////////////

let smap = new ShardMap<_,_>(numberStrings)
let bmap = Map<_,_>(numberStrings)

let dict = Dictionary<string,string>()
for (k,v) in numberStrings do
    dict.Add(k,v)

//////////////
for i in 0 .. 1000 do
    let bmap = Map<_,_>(numberStrings)
    ()

for i in 0 .. 1000 do
    let smap = new ShardMap<_,_>(numberStrings)
    ()

///////////////
let lookuploops = 10000

for i in 0 .. lookuploops do
    for (k,v) in numberStrings do
        if smap.[k] <> v then printfn "ERROR ON KEY MATCH: %A" k

for i in 0 .. lookuploops do
    for (k,v) in numberStrings do
        try 
            if dict.[k] <> v then
                printfn "ERROR ON KEY MATCH: %A" k
        with
        | e -> printfn "ERROR: %s >> %A" k e

for i in 0 .. lookuploops do
    for (k,v) in numberStrings do
        if bmap.[k] <> v then printfn "ERROR ON KEY MATCH: %A" k
        
////////////
let copyloops = 10000 * 1000
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

for i in 0 .. copyloops do
    let k,v = "Key1","Value1" 
    smap.Add(k,v)
    //ndict.Add(k,v)
    if not(smap.ContainsKey(k)) then failwith "failed to addadded value"

for i in 0 .. copyloops do
    let k,v = "Key1","Value1"
    let ndict = bmap.Add(k,v)
    if not(ndict.ContainsKey(k)) then failwith "new dict does not contain added value"
    if bmap.ContainsKey(k) then failwith "old dict has newly added value"

let bmap = bmap.Remove("Key1")

dict.Count   

smap.["Elekta"];;


#time