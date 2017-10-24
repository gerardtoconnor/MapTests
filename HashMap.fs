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

    member __.IncrRentals(rary:int []) =
        rary |> Array.Parallel.iter (fun ri ->
            if ri > 0 then rental.[ri] <- rental.[ri] + 1 
        )

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

///prvides index in bucket of shard
let inline private bucketIndex (keyHash:int,bitdepth:int) = (keyHash &&& (~~~(-1 <<< (bitdepth)))) >>> 3// todo: improve substring bitmask calc

///provides sub index in shards
let inline private shardIndex (keyHash:int) = keyHash &&& 0b111
let inline private isEmpty v = Object.ReferenceEquals(null,v)

type ShardMap<'K,'V  when 'K : equality and 'K : comparison>(buffer:Buffer8<Map<'K,'V>>,icount:int, nRIndex:int [],nBucket: Map<'K,'V> [] []) =
    
    let [<Literal>] InitialSize = 2 // 2 * 8 = 16 
    //let buffer = Buffer8Factory.GetBuffer8<Map<'K,'V>>()
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

    let mutable count = icount 

    //let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))

    let mutable bitMaskDepth = calcBitMaskDepth icount
    
    let calcpBitMask (bitDepth:int) = ~~~(-1 <<< (bitDepth))
    let mutable pBitMask = calcpBitMask bitMaskDepth
    ///provides index in local bucket of shard


    let higherRange (index:int,bitdepth:int) = (index ||| 1 <<< bitdepth) >>> 3  

    let item (key:'K) =
        let kh = key.GetHashCode()
        let bi = bucketIndex(kh,bitMaskDepth)
        let si = shardIndex kh
        let m = bucket.[bi].[si]
        //printfn "?| looking for key:'%A' [%i][%i] in map{%A}" key bi si m
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
                let newBucket = Array.zeroCreate<Map<'K,'V> []> (isize * 2)
                let newRIndex = Array.zeroCreate<int> (isize * 2) // <<< todo: change to create -1s so rindex can be checked processing and at end
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
        let bi = bucketIndex(kh,bitMaskDepth)
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

        buffer.IncrRentals(rindex)

        ShardMap<'K,'V>(buffer,count,nRIndex,nBucket)
                
    member __.Item(key:'K) =
        if resizing then
            lock resizeLock (fun () -> item key)
        else
            item key

    member __.ContainsKey(key:'K) =
        let kh = key.GetHashCode()
        let m = bucket.[bucketIndex(kh,bitMaskDepth)].[shardIndex kh]
        //printfn "?| looking for key:'%A' [%i][%i] in map{%A}" key bi si m
        if isEmpty m then
            false
        else
            m.ContainsKey key               

    interface IDisposable with
        member __.Dispose() =
            for i in 0 .. bucket.Length - 1 do
                buffer.Return(rindex.[i],bucket.[i])

    new(kvps:('K * 'V) seq) =

        let buffer = Buffer8Factory.GetBuffer8<Map<'K,'V>>() //duplication can constructor not access internal fields!? should this be provided in main ctor
        let mutable counter = 0
        let mutable items = []
        kvps |> Seq.iter (fun kvp -> 
            counter <- counter + 1
            items <- kvp :: items
        )
        
        let bitdepth = calcBitMaskDepth counter
        let bucketSize = pow2 bitdepth
        let newBucket = Array.zeroCreate<Map<'K,'V> []>(bucketSize)
        let newRIndex = Array.create bucketSize -1 // set and empty state for every bucket without pulling in empty arrays yet
        
        items
        |> List.iter (fun (k,v) -> 
                let kh = k.GetHashCode()
                let bi = bucketIndex(kh,bitdepth)
                let shrd =
                    if newRIndex.[bi] = -1 then
                        buffer.Rent(bi,newRIndex,newBucket)
                    else
                        newBucket.[bi]
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
        for bi in 0.. bucketSize - 1 do
            if newRIndex.[bi] = -1 then
                newBucket.[bi] <- buffer.Empty() |> snd
        
        ShardMap<'K,'V>(buffer,counter,newRIndex,newBucket)
        


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

let testSeq = [
    ("Cooper Energy","Oil & Gas");
    ("Asetek","Hardware");
    ("Shire","Healthcare");
    ("AB InBev","Food & Beverage");
    ("Vodafone","Mobile Telecommunications");
    ("Akzo Nobel","Chemicals");
    ("Bayer","Healthcare");
    ("Liberty Global C Class","Media");
    ("Tele Columbus","Media");
    ("Ryanair","Travel/Leisure");
    ("SAP","Software");
    ("Vivendi","Media");
    ("Leonardo","Aerospace/Defense");
    ("Telecom Italia","Fixed-Line Telecommunications");
    ("UniCredit","Banking");
    ("Aker BP","Oil & Gas");
    ("Volvo","Industrial Machinery");
    ("Alstom","Diversified Manufacturing");
    ("LafargeHolcim","Building Materials");
    ("Danone","Food & Beverage");
    ("ASML Holdings","Semiconductors");
    ("IMCD","Chemicals");
    ("Reckitt Benckiser","Cosmetics & Toiletries");
    ("Fresenius Medical Care","Healthcare");
    ("Deutsche Telekom","Fixed-Line Telecommunications");
    ("Nokia","Telecommunications Equipment");
    ("Royal Dutch Shell","Oil & Gas");
    ("AIB","Banking");
    ("Whitbread","Travel/Leisure");
    ("Renault","Automotive");
    ("Daimler","Automotive");
    ("Barclays","Banking");
    ("Brenntag","Chemicals");
    ("Glenveagh","Construction");
    ("LiLAC C Class","Media");
    ("Awilco LNG","Transport");
    ("Zeta Petroleum","Oil & Gas");
    ("OMV","Oil & Gas");
    ("Kuehne & Nagel","Transport");
    ("Statoilhydro","Oil & Gas");
    ("Sandvik AB","Industrial Machinery");
    ("Airbus","Aerospace/Defense");
    ("Merck","Chemicals");
    ("Wartsila","Industrial Machinery");
    ("Securitas","Business Services");
    ("Dassault Systemes","Software");
    ("Colruyt","General Retail");
    ("Just Eat","Internet");
    ("Kone","Construction");
    ("Swisscom","Fixed-Line Telecommunications");
    ("Solvay","Chemicals");
    ("EDF","Utilities");
    ("Electrolux","Consumer Durables");
    ("SKF","Industrial Machinery");
    ("Elekta","Healthcare");
]

let smap = ShardMap<_,_>(testSeq)
let dict = Dictionary<string,string>()

for i in 0 .. 1000 do
    let bmap = Map<_,_>(numberStrings)
    ()

for i in 0 .. 1000 do
    let smap = new ShardMap<_,_>(numberStrings)
    ()

for (k,v) in numberStrings do
    dict.Add(k,v)

for (k,v) in numberStrings do
    dict.Add(k,v)

for i in 0 .. 100000 do
    for (k,v) in numberStrings do
        try 
            if smap.[k] <> v then
                 printfn "ERROR ON KEY MATCH: %A" k
        with
        | e -> printfn "ERROR: %s >> %A" k e

for i in 0 .. 100000 do
    for (k,v) in numberStrings do
        try 
            if dict.[k] <> v then
                printfn "ERROR ON KEY MATCH: %A" k
        with
        | e -> printfn "ERROR: %s >> %A" k e

for i in 0 .. 100000 do
    for (k,v) in numberStrings do
        try 
            if bmap.[k] <> v then
                printfn "ERROR ON KEY MATCH: %A" k
        with
        | e -> printfn "ERROR: %s >> %A" k e

for i in 0 .. 1000 do
    let ndict = Dictionary<_,_>(dict)
    let k,v = "Key1","Value1" 
    ndict.Add(k,v)
    if not(ndict.ContainsKey(k)) || dict.ContainsKey(k) then failwith "Immutablity Error"


for i in 0 .. 1000 do
    let ndict = smap.Copy()
    let k,v = "Key1","Value1" 
    ndict.Add(k,v)
    if not(ndict.ContainsKey(k)) then failwith "new dict does not contain added value"
    if smap.ContainsKey(k) then failwith "old dict has newly added value"

for i in 0 .. 1000 do
    let ndict = 
    let k,v = "Key1","Value1" 
    ndict.Add(k,v)
    if not(ndict.ContainsKey(k)) then failwith "new dict does not contain added value"
    if smap.ContainsKey(k) then failwith "old dict has newly added value"

dict.Count   

smap.["Elekta"];;


#time