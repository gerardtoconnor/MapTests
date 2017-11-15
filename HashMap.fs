module HashMap

open MapOld.MapTree
open MapTree
open System.Threading.Tasks
open System.Security.Cryptography.X509Certificates

#nowarn "51"
#nowarn "69" // interface implementations in augmentations
#nowarn "60" // override implementations in augmentations


////////////////////////////
/// Map Tree
///////////////////////////

open Microsoft.FSharp.Core
open Microsoft.FSharp.Core.Operators
open Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators
open System
open System.Threading
open System.Collections.Generic
open System.Collections.Concurrent
// open Internal.Utilities
// open Internal.Utilities.Collections


//[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
[<NoEquality; NoComparison>]
type private MapTree<'Key,'T> = 
    | MapEmpty
    | MapOne of 'Key * 'T
    | MapNode of 'Key * 'T * MapTree<'Key,'T> *  MapTree<'Key,'T> * int


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private MapTree = 

    let rec sizeAux acc m = 
        match m with  
        | MapEmpty -> acc       
        | MapOne _ -> acc + 1
        | MapNode(_,_,l,r,_) -> sizeAux (sizeAux (acc+1) l) r 

    let size x = sizeAux 0 x


#if TRACE_SETS_AND_MAPS
    let mutable traceCount = 0
    let mutable numOnes = 0
    let mutable numNodes = 0
    let mutable numAdds = 0
    let mutable numRemoves = 0
    let mutable numLookups = 0
    let mutable numUnions = 0
    let mutable totalSizeOnNodeCreation = 0.0
    let mutable totalSizeOnMapAdd = 0.0
    let mutable totalSizeOnMapLookup = 0.0
    let mutable largestMapSize = 0
    let mutable largestMapStackTrace = Unchecked.defaultof<_>
    let report() = 
       traceCount <- traceCount + 1 
       if traceCount % 1000000 = 0 then 
           System.Console.WriteLine("#MapOne = {0}, #MapNode = {1}, #Add = {2}, #Remove = {3}, #Unions = {4}, #Lookups = {5}, avMapTreeSizeOnNodeCreation = {6}, avMapSizeOnCreation = {7}, avMapSizeOnLookup = {8}",numOnes,numNodes,numAdds,numRemoves,numUnions,numLookups,(totalSizeOnNodeCreation / float (numNodes + numOnes)),(totalSizeOnMapAdd / float numAdds),(totalSizeOnMapLookup / float numLookups))
           System.Console.WriteLine("#largestMapSize = {0}, largestMapStackTrace = {1}",largestMapSize, largestMapStackTrace)

    let MapOne n = 
        report(); 
        numOnes <- numOnes + 1; 
        totalSizeOnNodeCreation <- totalSizeOnNodeCreation + 1.0; 
        MapTree.MapOne n

    let MapNode (x,l,v,r,h) = 
        report(); 
        numNodes <- numNodes + 1; 
        let n = MapTree.MapNode(x,l,v,r,h)
        totalSizeOnNodeCreation <- totalSizeOnNodeCreation + float (size n); 
        n
#endif

    let empty = MapEmpty 

    let height  = function
      | MapEmpty -> 0      
      | MapOne _ -> 1
      | MapNode(_,_,_,_,h) -> h

    let isEmpty m = 
        match m with 
        | MapEmpty -> true
        | _ -> false

    let mk l k v r = 
        match l,r with 
        | MapEmpty,MapEmpty -> MapOne(k,v)
        | _ -> 
            let hl = height l 
            let hr = height r 
            let m = if hl < hr then hr else hl 
            MapNode(k,v,l,r,m+1)

    let rebalance t1 k v t2 =
        let t1h = height t1 
        let t2h = height t2 
        if  t2h > t1h + 2 then (* right is heavier than left *)
            match t2 with 
            | MapNode(t2k,t2v,t2l,t2r,_) -> 
               (* one of the nodes must have height > height t1 + 1 *)
               if height t2l > t1h + 1 then  (* balance left: combination *)
                 match t2l with 
                 | MapNode(t2lk,t2lv,t2ll,t2lr,_) ->
                    mk (mk t1 k v t2ll) t2lk t2lv (mk t2lr t2k t2v t2r) 
                 | _ -> failwith "rebalance"
               else (* rotate left *)
                 mk (mk t1 k v t2l) t2k t2v t2r
            | _ -> failwith "rebalance"
        else
            if  t1h > t2h + 2 then (* left is heavier than right *)
              match t1 with 
              | MapNode(t1k,t1v,t1l,t1r,_) -> 
                (* one of the nodes must have height > height t2 + 1 *)
                  if height t1r > t2h + 1 then 
                  (* balance right: combination *)
                    match t1r with 
                    | MapNode(t1rk,t1rv,t1rl,t1rr,_) ->
                        mk (mk t1l t1k t1v t1rl) t1rk t1rv (mk t1rr k v t2)
                    | _ -> failwith "rebalance"
                  else
                    mk t1l t1k t1v (mk t1r k v t2)
              | _ -> failwith "rebalance"
            else mk t1 k v t2

    let rec add (comparer: IComparer<'Value>) k v m = 
        match m with 
        | MapEmpty -> MapOne(k,v)       
        | MapOne(k2,_) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0   then MapNode (k,v,MapEmpty,m,2)
            elif c = 0 then MapOne(k,v)
            else            MapNode (k,v,m,MapEmpty,2)
        | MapNode(k2,v2,l,r,h) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0 then rebalance (add comparer k v l) k2 v2 r
            elif c = 0 then MapNode(k,v,l,r,h)
            else rebalance l k2 v2 (add comparer k v r) 

    let rec find (comparer: IComparer<'Value>) k m = 
        match m with 
        | MapEmpty -> raise (KeyNotFoundException())
        | MapOne(k2,v2) -> 
            let c = comparer.Compare(k,k2) 
            if c = 0 then v2
            else raise (KeyNotFoundException())
        | MapNode(k2,v2,l,r,_) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0 then find comparer k l
            elif c = 0 then v2
            else find comparer k r

    let rec tryFind (comparer: IComparer<'Value>) k m = 
        match m with 
        | MapEmpty -> None
        | MapOne(k2,v2) -> 
            let c = comparer.Compare(k,k2) 
            if c = 0 then Some v2
            else None
        | MapNode(k2,v2,l,r,_) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0 then tryFind comparer k l
            elif c = 0 then Some v2
            else tryFind comparer k r

    let partition1 (comparer: IComparer<'Value>) (f:OptimizedClosures.FSharpFunc<_,_,_>) k v (acc1,acc2) = 
        if f.Invoke(k, v) then (add comparer k v acc1,acc2) else (acc1,add comparer k v acc2) 
    
    let rec partitionAux (comparer: IComparer<'Value>) (f:OptimizedClosures.FSharpFunc<_,_,_>) s acc = 
        match s with 
        | MapEmpty -> acc
        | MapOne(k,v) -> partition1 comparer f k v acc
        | MapNode(k,v,l,r,_) -> 
            let acc = partitionAux comparer f r acc 
            let acc = partition1 comparer f k v acc
            partitionAux comparer f l acc

    let partition (comparer: IComparer<'Value>) f s = partitionAux comparer (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) s (empty,empty)

    let filter1 (comparer: IComparer<'Value>) (f:OptimizedClosures.FSharpFunc<_,_,_>) k v acc = if f.Invoke(k, v) then add comparer k v acc else acc 

    let rec filterAux (comparer: IComparer<'Value>) (f:OptimizedClosures.FSharpFunc<_,_,_>) s acc = 
        match s with 
        | MapEmpty -> acc
        | MapOne(k,v) -> filter1 comparer f k v acc
        | MapNode(k,v,l,r,_) ->
            let acc = filterAux comparer f l acc
            let acc = filter1 comparer f k v acc
            filterAux comparer f r acc

    let filter (comparer: IComparer<'Value>) f s = filterAux comparer (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) s empty

    let rec spliceOutSuccessor m = 
        match m with 
        | MapEmpty -> failwith "internal error: Map.spliceOutSuccessor"
        | MapOne(k2,v2) -> k2,v2,MapEmpty
        | MapNode(k2,v2,l,r,_) ->
            match l with 
            | MapEmpty -> k2,v2,r
            | _ -> let k3,v3,l' = spliceOutSuccessor l in k3,v3,mk l' k2 v2 r

    let rec remove (comparer: IComparer<'Value>) k m = 
        match m with 
        | MapEmpty -> empty
        | MapOne(k2,_) -> 
            let c = comparer.Compare(k,k2) 
            if c = 0 then MapEmpty else m
        | MapNode(k2,v2,l,r,_) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0 then rebalance (remove comparer k l) k2 v2 r
            elif c = 0 then 
              match l,r with 
              | MapEmpty,_ -> r
              | _,MapEmpty -> l
              | _ -> 
                  let sk,sv,r' = spliceOutSuccessor r 
                  mk l sk sv r'
            else rebalance l k2 v2 (remove comparer k r) 

    let rec mem (comparer: IComparer<'Value>) k m = 
        match m with 
        | MapEmpty -> false
        | MapOne(k2,_) -> (comparer.Compare(k,k2) = 0)
        | MapNode(k2,_,l,r,_) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0 then mem comparer k l
            else (c = 0 || mem comparer k r)

    let rec iterOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m =
        match m with 
        | MapEmpty -> ()
        | MapOne(k2,v2) -> f.Invoke(k2, v2)
        | MapNode(k2,v2,l,r,_) -> iterOpt f l; f.Invoke(k2, v2); iterOpt f r

    let iter f m = iterOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec tryPickOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m =
        match m with 
        | MapEmpty -> None
        | MapOne(k2,v2) -> f.Invoke(k2, v2) 
        | MapNode(k2,v2,l,r,_) -> 
            match tryPickOpt f l with 
            | Some _ as res -> res 
            | None -> 
            match f.Invoke(k2, v2) with 
            | Some _ as res -> res 
            | None -> 
            tryPickOpt f r

    let tryPick f m = tryPickOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec existsOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m = 
        match m with 
        | MapEmpty -> false
        | MapOne(k2,v2) -> f.Invoke(k2, v2)
        | MapNode(k2,v2,l,r,_) -> existsOpt f l || f.Invoke(k2, v2) || existsOpt f r

    let exists f m = existsOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec forallOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m = 
        match m with 
        | MapEmpty -> true
        | MapOne(k2,v2) -> f.Invoke(k2, v2)
        | MapNode(k2,v2,l,r,_) -> forallOpt f l && f.Invoke(k2, v2) && forallOpt f r

    let forall f m = forallOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec map f m = 
        match m with 
        | MapEmpty -> empty
        | MapOne(k,v) -> MapOne(k,f v)
        | MapNode(k,v,l,r,h) -> 
            let l2 = map f l 
            let v2 = f v 
            let r2 = map f r 
            MapNode(k,v2,l2, r2,h)

    let rec mapiOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m = 
        match m with
        | MapEmpty -> empty
        | MapOne(k,v) -> MapOne(k, f.Invoke(k, v))
        | MapNode(k,v,l,r,h) -> 
            let l2 = mapiOpt f l 
            let v2 = f.Invoke(k, v) 
            let r2 = mapiOpt f r 
            MapNode(k,v2, l2, r2,h)

    let mapi f m = mapiOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec foldBackOpt (f:OptimizedClosures.FSharpFunc<_,_,_,_>) m x = 
        match m with 
        | MapEmpty -> x
        | MapOne(k,v) -> f.Invoke(k,v,x)
        | MapNode(k,v,l,r,_) -> 
            let x = foldBackOpt f r x
            let x = f.Invoke(k,v,x)
            foldBackOpt f l x

    let foldBack f m x = foldBackOpt (OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(f)) m x

    let rec foldOpt (f:OptimizedClosures.FSharpFunc<_,_,_,_>) x m  = 
        match m with 
        | MapEmpty -> x
        | MapOne(k,v) -> f.Invoke(x,k,v)
        | MapNode(k,v,l,r,_) -> 
            let x = foldOpt f x l
            let x = f.Invoke(x,k,v)
            foldOpt f x r

    let fold f x m = foldOpt (OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(f)) x m

    let foldSectionOpt (comparer: IComparer<'Value>) lo hi (f:OptimizedClosures.FSharpFunc<_,_,_,_>) m x =
        let rec foldFromTo (f:OptimizedClosures.FSharpFunc<_,_,_,_>) m x = 
            match m with 
            | MapEmpty -> x
            | MapOne(k,v) ->
                let cLoKey = comparer.Compare(lo,k)
                let cKeyHi = comparer.Compare(k,hi)
                let x = if cLoKey <= 0 && cKeyHi <= 0 then f.Invoke(k, v, x) else x
                x
            | MapNode(k,v,l,r,_) ->
                let cLoKey = comparer.Compare(lo,k)
                let cKeyHi = comparer.Compare(k,hi)
                let x = if cLoKey < 0                 then foldFromTo f l x else x
                let x = if cLoKey <= 0 && cKeyHi <= 0 then f.Invoke(k, v, x) else x
                let x = if cKeyHi < 0                 then foldFromTo f r x else x
                x
       
        if comparer.Compare(lo,hi) = 1 then x else foldFromTo f m x

    let foldSection (comparer: IComparer<'Value>) lo hi f m x =
        foldSectionOpt comparer lo hi (OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(f)) m x

    let toList m = 
        let rec loop m acc = 
            match m with 
            | MapEmpty -> acc
            | MapOne(k,v) -> (k,v)::acc
            | MapNode(k,v,l,r,_) -> loop l ((k,v)::loop r acc)
        loop m []
    let toArray m = m |> toList |> Array.ofList
    let ofList comparer l = List.fold (fun acc (k,v) -> add comparer k v acc) empty l

    let rec mkFromEnumerator comparer acc (e : IEnumerator<_>) = 
        if e.MoveNext() then 
            let (x,y) = e.Current 
            mkFromEnumerator comparer (add comparer x y acc) e
        else acc
      
    let ofArray comparer (arr : array<_>) =
        let mutable res = empty
        for (x,y) in arr do
            res <- add comparer x y res 
        res

    let ofSeq comparer (c : seq<'Key * 'T>) =
        match c with 
        | :? array<'Key * 'T> as xs -> ofArray comparer xs
        | :? list<'Key * 'T> as xs -> ofList comparer xs
        | _ -> 
            use ie = c.GetEnumerator()
            mkFromEnumerator comparer empty ie 
      
    let copyToArray s (arr: _[]) i =
        let j = ref i 
        s |> iter (fun x y -> arr.[!j] <- KeyValuePair(x,y); j := !j + 1)

    let rec addAndIncr (comparer: IComparer<'Value>) k v (iref:int ref) m = 
        match m with 
        | MapEmpty -> Interlocked.Increment(iref) |> ignore ; MapOne(k,v)       
        | MapOne(k2,_) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0   then Interlocked.Increment(iref) |> ignore ; MapNode (k,v,MapEmpty,m,2)
            elif c = 0 then MapOne(k,v)
            else            Interlocked.Increment(iref) |> ignore ; MapNode (k,v,m,MapEmpty,2)
        | MapNode(k2,v2,l,r,h) -> 
            let c = comparer.Compare(k,k2) 
            if c < 0 then rebalance (addAndIncr comparer k v iref l) k2 v2 r
            elif c = 0 then MapNode(k,v,l,r,h)
            else rebalance l k2 v2 (addAndIncr comparer k v iref r) 
    


////////////////////////////
////////////////////////
///Shard Map
////////////////////
///////////////////////////

type Shard<'K,'V> = MapTree<'K,'V> []
type Bucket<'K,'V> = Shard<'K,'V> []

type MutateHead<'V>(head) =
    let mutable head : 'V list = [head]
    member __.Add(v:'V) = head <- v :: head
    member __.Head with get() = head


open System.Collections.Generic
open System
open NonStructuralComparison

[<Literal>] 
let private ShardSize = 16
//let private empty = Array.zeroCreate<Map<'K,'V>>(ShardSize)

// Helper Functions
////////////////////////////

//let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2))) //todo:make private
let inline calcBitMaskDepth itemCount =
    let rec go s d =
        if s = 0 then d
        else go (s >>> 1) (d + 1)
    go itemCount 0
   
let inline private pow2 (i:int) = 2 <<< (i - 5) // todo 4 is shard size 2^n
let inline calcSubBitMask (bitDepth:int) = ~~~(-1 <<< (bitDepth))

///prvides index in bucket of shard
let inline private bucketIndex (keyHash:int,subBitMask:int) = (keyHash &&& subBitMask) >>> 4// todo: improve substring bitmask calc

///let inline private bucketIndexOld (keyHash:int,bitdepth:int) = (keyHash &&& (~~~(-1 <<< (bitdepth)))) >>> 4// todo: improve substring bitmask calc

///provides sub index in shards
let inline private shardIndex (keyHash:int) = keyHash &&& 0b1111
let inline private isEmpty v = Object.ReferenceEquals(null,v)

let inline private higherRange (index:int,bitdepth:int) = (index ||| (1 <<< (bitdepth - 4)))

let inline private newShardEmpty () = Array.zeroCreate<MapTree<'K,'V>>(ShardSize)
let inline private newBucketEmpty bucketSize = Array.zeroCreate<Shard<'K,'V>>(bucketSize)

let private eachMapInBucket (bucket:Bucket<'K,'V>,f:int -> int -> MapTree<'K,'V> -> unit) =
    let fo = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(f)
    
    Tasks.Parallel.For(0, bucket.Length, fun bi ->
        for si in 0 .. ShardSize - 1 do
            let s = bucket.[bi]
            if not(isEmpty s) then
                let m = s.[si]
                if not(isEmpty m) then
                    fo.Invoke(bi,si,m)
    ) |> ignore

let private getOrCreateShard (bucket:Bucket<'K,'V>,index:int) =
    let mutable shrd = bucket.[index]
    if isEmpty shrd then
        shrd <- newShardEmpty ()
        bucket.[index] <- shrd
    shrd        

    
/// Shard Map
////////////////////////////

type ShardMap<'K,'V  when 'K : equality and 'K : comparison >(icount:int, nBucket:Shard<'K,'V> []) =

    let empty = newShardEmpty ()

    //let mutable subMapHead = ihead
    let comparer = LanguagePrimitives.FastGenericComparer<'Key>

    let mutable bucket = nBucket
    let countRef = ref icount

    //Lock variables
    ///////////////////////////////////
    let mutable resizing = false // lightweight single op read var for checking state
    let resizeLock = obj()  // lock for when internal bucket array needs to resize


    //let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))

    let mutable capacity = (bucket.Length * ShardSize) - 1
    let mutable bitMaskDepth = (calcBitMaskDepth capacity)
    let mutable bucketBitMask = calcSubBitMask bitMaskDepth    
    let mutable mapCache = []
    let mutable mapCacheRun = false

    /// Internal Funtions
    /////////////////////////////////////////////////
    let cacheReset () = 
        mapCache <- []
        mapCacheRun <- false
    
    let newShardCopy oary = 
        let nary = newShardEmpty ()
        Array.Copy(oary,nary,ShardSize)
        nary

    let mapList () =
        // match mapCache with
        // | [] -> 
            //printfn "Building Map Cache List..."
            let mutable result = []
            for bi in 0 .. bucket.Length - 1 do
                for si in 0 .. ShardSize - 1 do
                    if not(isEmpty bucket.[bi].[si]) then
                        result <- bucket.[bi].[si] :: result
            mapCache <- result
            mapCacheRun <- true
            result                                 
        // | result -> 
        //     result

    let getMap (key:'K) =
        let kh = key.GetHashCode()
        bucket.[bucketIndex(kh,bucketBitMask)].[shardIndex kh]

    let item (key:'K) =
        let m = getMap key
        if isEmpty m then
            raise <| KeyNotFoundException(sprintf "Key:%A , does not exist in the dictionary" key)
        else
            MapTree.find comparer key m

    let tryFind (key:'K) =
        let m = getMap key
        if isEmpty m then
            None
        else
            MapTree.tryFind comparer key m

    let bprint (v:int) = Convert.ToString(v, 2)  // todo: remove, only needed for debugging

    let resize () =

        //printfn "started resize ()"
        let isize = bucket.Length
        let nsize = isize * 2
        let ibmd = bitMaskDepth
        
        //printfn "ibmd : %i / isize: %i" ibmd isize
        
        let newBucket = Array.zeroCreate<Shard<'K,'V>> (nsize)
        //printfn "new bucket of %i size created" nsize
        
        Tasks.Parallel.For(0, bucket.Length, 
            fun i0 ->

            //for i0 in 0 .. bucket.Length - 1 do // for each shard in old bucket
                //printfn "newBucket starting %i : %A" i0 newBucket
                let oshrd = bucket.[i0]  //get old shard at index
                let i1 = higherRange(i0,ibmd)
                //printfn "for range i:%i {%s}, higher range i2:%i {%s}" bi (bprint bi) i2 (bprint i2)
                if Object.ReferenceEquals(oshrd,empty) then // special empty shard case
                    newBucket.[i0] <- empty
                    newBucket.[i1] <- empty

                else // shard needs to be split out amoungst two new shards

                    for j in 0 .. ShardSize - 1 do
                        let m = oshrd.[j]
                        if not(isEmpty m) then
                            let m1,m0 = MapTree.partition comparer (fun k _ -> ((k.GetHashCode() >>> (ibmd )) &&& 0b1) = 1) m //<<<CHECK
                            
                            if not (MapTree.isEmpty m0) then
                                let shrd0 = getOrCreateShard( newBucket, i0)
                                if isEmpty shrd0.[j] then
                                    shrd0.[j] <- m0
                                
                            if not (MapTree.isEmpty m1) then
                                let shrd1 = getOrCreateShard( newBucket , i1)
                                if isEmpty shrd1.[j] then
                                    shrd1.[j] <- m1
        ) |> ignore                            
                            
        // after copying, check if buckets still empty and add empty shard if null
        for i2 in 0 .. newBucket.Length - 1 do
            if isEmpty newBucket.[i2] then newBucket.[i2] <- empty
            
        //now update internal state
        lock bucket.SyncRoot (fun () -> bucket <- newBucket ) // ??? needed with resize lock already in place?
        bitMaskDepth <- calcBitMaskDepth !countRef
        bucketBitMask <- calcSubBitMask bitMaskDepth
        capacity <- (newBucket.Length * ShardSize) - 1
        //printfn "finished resizing operations"


    let add(k:'K,v:'V) =
        let kh = k.GetHashCode()
        let bi = bucketIndex(kh,bucketBitMask)
        let si = shardIndex kh
        let shrd = newShardCopy bucket.[bi]

        lock bucket.SyncRoot (fun () -> bucket.[bi] <- shrd)

        let m = shrd.[si]
        if isEmpty m then
            countRef := Interlocked.Increment(countRef)
            let nm = MapOne (k,v)
            shrd.[si] <- nm
            if mapCacheRun then mapCache <- nm :: mapCache // <<
        else
            if not(MapTree.mem comparer k m) then 
                countRef := Interlocked.Increment(countRef)
            let nm = MapTree.add comparer k v m
            shrd.[si] <- nm
            cacheReset () // no clean way to rip out the previous 'm' map so need to clear cache

    let remove(k:'K) =
        let kh = k.GetHashCode()
        let bi = bucketIndex(kh,bucketBitMask)
        let si = shardIndex kh
        let shrd = newShardCopy bucket.[bi]
        
        lock bucket.SyncRoot (fun () -> bucket.[bi] <- shrd )

        cacheReset()  // clear the mapCache, next call to seq can rebuild with new map refs

        let m = shrd.[si]
        if isEmpty m then
            raise <| KeyNotFoundException(sprintf "Key:'%A' not found in map so cannot remove" k)
        else
            Interlocked.Decrement(countRef) |> ignore
            shrd.[si] <- MapTree.remove comparer k m
   
    // let transpose (fn:MapTree<'K,'V> -> MapTree<'K,'T>) =
    //     let nBucket = Array.zeroCreate<Shard<'K,'T>>(bucket.Length)

    //     eachMapInBucket(bucket, fun bi si m -> 
    //         let s = getOrCreateShard (nBucket,bi)
    //         s.[si] <- fn m
    //     )
    //     ShardMap<'K,'T>(!countRef,nBucket)

    let mapFold (foldFn:'S -> 'K -> 'V  -> 'S) (istate:'S) = 
        let foldOpt = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(foldFn)

        let rec gmp(m,acc) = 
            match m with
            | MapEmpty -> acc
            | MapOne (k,v) -> foldOpt.Invoke(acc,k,v)
            | MapNode(k,v,l,r,_) ->
                gmp(r,
                    gmp(l,
                        foldOpt.Invoke(acc,k,v)))
        let rec gls (ls,acc) =
            match ls with
            | [] -> acc
            | h :: t -> gls(t,gmp(h,acc))                 
        gls(mapList() , istate)

    let exists (existsFn:'K -> 'V  -> bool) = 
        let fnOpt = OptimizedClosures.FSharpFunc<_,_,_>.Adapt(existsFn)

        let rec hop(bi,si) =
            let next(bi,si) = 
                if   si + 1 < ShardSize     then hop(bi    ,si + 1)
                elif bi + 1 < bucket.Length then hop(bi + 1,0     )
                else false
            let m = bucket.[bi].[si]
            if isEmpty m then
                next(bi,si)
            else
                if MapTree.existsOpt fnOpt m then
                    true
                else
                    next(bi,si)
        hop(0,0)

    let tryFindInRange (fn:'V -> bool) =
        let rec hop(bi,si) =
            let next(bi,si) = 
                if   si + 1 < ShardSize     then hop(bi,si + 1)
                elif bi + 1 < bucket.Length then hop(bi + 1,0)
                else None               
            let rec go ml =
                match ml with
                | [] -> next(bi,si)
                | m :: t ->
                    match m with 
                    | MapEmpty ->           go t
                    | MapOne(_,v) ->        if fn v then Some v else go t
                    | MapNode(_,v,l,r,_) -> if fn v then Some v else go (l :: r :: t)                
            let m = bucket.[bi].[si]
            if isEmpty m then next(bi,si)
            else go [m]      
        hop(0,0)

    let keySet fn h k (nBucket:Shard<'K,'T> []) =
        let hk = k.GetHashCode()
        let bi = bucketIndex(hk,bucketBitMask)
        if isEmpty nBucket.[bi] then
            nBucket.[bi] <- Array.zeroCreate<MapTree<'K,'T>>(ShardSize)
        nBucket.[bi].[shardIndex(hk)] <- fn h


    /////////////////////////////////////////////////////////////
    /// Constructor operation to ensure no null array references
    /////////////////////////////////////////////////////////////
        
    do  // prevent any out of index errors on non-set shards
        for bi in 0.. bucket.Length - 1 do
        if isEmpty bucket.[bi] then
            bucket.[bi] <- empty

    static member private transpose (fn:MapTree<'K,'V> -> MapTree<'K,'T>) (itemCount:int) (bucket:Shard<'K,'V> []) =
        let nBucket = Array.zeroCreate<Shard<'K,'T>>(bucket.Length)
        
        eachMapInBucket(bucket, fun bi si m -> 
            let s = getOrCreateShard (nBucket,bi)
            s.[si] <- fn m
        )
        ShardMap<'K,'T>(itemCount,nBucket)

    member __.Add(k:'K,v:'V) =     
                
        if resizing then
            lock resizeLock (fun () -> add(k,v))
        else
            if !countRef > capacity then
            // base array needs resizing
                resizing <- true
                lock resizeLock resize 
                //End of Lock
                resizing <- false
            add(k,v)

    member __.Remove(k:'K) =
        if resizing then
            lock resizeLock (fun () -> remove(k))
        else
            remove(k)


    member __.Copy() =        
        let newbucket = Array.zeroCreate<Shard<'K,'V>>(bucket.Length)
        Array.Copy(bucket,newbucket,bucket.Length)
        ShardMap<'K,'V>(!countRef,newbucket)
                
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
            MapTree.mem comparer key m

    member __.TryFind(key:'K) =
        if resizing then
            lock resizeLock (fun () -> tryFind key)
        else
            tryFind key

    member __.Iter(fn:'K -> 'V -> unit) =
        let iopt = OptimizedClosures.FSharpFunc<_,_,_>.Adapt(fn)
        eachMapInBucket(bucket,fun _ _ m ->
            MapTree.iterOpt iopt m
        )
    //member __.Fold (foldFn:'S -> 'K -> 'V  -> 'S) (istate:'S) = mapFold foldFn istate

    member __.Fold (foldFn:'S -> 'K -> 'V  -> 'S) (istate:'S) =
        let foldOpt = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(foldFn)

        let rec gmp(m,acc) = 
            match m with
            | MapEmpty -> acc
            | MapOne (k,v) -> foldOpt.Invoke(acc,k,v)
            | MapNode(k,v,l,r,_) ->
                gmp(r,
                    gmp(l,
                        foldOpt.Invoke(acc,k,v)))
        
        let mutable state = istate 
        for bi in 0 .. bucket.Length - 1 do
            for si in 0 .. ShardSize - 1 do
                if isEmpty bucket.[bi].[si] then ()
                else
                    state <- gmp(bucket.[bi].[si],state)
        state

    [<Obsolete("Folds in same random order as fold but matches foldback fn signature of accumulator state last")>]
    member __.FoldBack (foldFn:'K -> 'V  -> 'S ->'S) (istate:'S) =
        let foldOpt = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(foldFn)

        let rec gmp(m,acc) = 
            match m with
            | MapEmpty -> acc
            | MapOne (k,v) -> foldOpt.Invoke(k,v,acc)
            | MapNode(k,v,l,r,_) ->
                gmp(r,
                    gmp(l,
                        foldOpt.Invoke(k,v,acc)))
        
        let mutable state = istate 
        for bi in 0 .. bucket.Length - 1 do
            for si in 0 .. ShardSize - 1 do
                if not(isEmpty bucket.[bi].[si]) then 
                    state <- gmp(bucket.[bi].[si],state)
        state
    
    member __.Partition (predicate:'K -> 'V -> bool) =
        let predOpt = OptimizedClosures.FSharpFunc<_,_,_>.Adapt(predicate)
        let bt = Array.zeroCreate<Shard<'K,'V>>(bucket.Length)
        let ct = ref 0
        let bf = Array.zeroCreate<Shard<'K,'V>>(bucket.Length)
        let cf = ref 0

        Tasks.Parallel.For(0,bucket.Length,fun bi ->
            let shrd = bucket.[bi]
            for si in 0 .. ShardSize - 1 do
                let m = shrd.[si]
                if not(isEmpty m) then
                    MapTree.iter (fun k v ->
                        let mapResult(b0:Bucket<'K,'V>,cRef:int ref) = 
                            Interlocked.Increment(cRef) |> ignore
                            let s0 = getOrCreateShard(b0 , bi)
                            let m0 = s0.[si]
                            s0.[si] <-
                                if isEmpty m0 then
                                    MapOne(k,v)
                                else
                                    MapTree.add comparer k v m0
                        if predOpt.Invoke(k,v) then
                            mapResult(bt,ct)
                        else
                            mapResult(bf,cf)
                    ) m
            // after shard map filled, fill in empties
            if isEmpty bt then bt.[bi] <- empty
            if isEmpty bf then bf.[bi] <- empty
                            
        ) |> ignore
        
        ShardMap<'K,'V>(!ct,bt) , ShardMap<'K,'V>(!cf,bf)

    member __.Map (mapFn:'V -> 'T) : ShardMap<'K,'T> = ShardMap.transpose (MapTree.map mapFn) !countRef bucket
    
////////////////
    member __.toSeq () =

        let mutable stack = mapList ()
        let mutable current = Unchecked.defaultof<KeyValuePair<_,_>>

        { new IEnumerator<_> with 
                member self.Current = current
            interface System.Collections.IEnumerator with
                  member self.Current = box self.Current
                  member self.MoveNext() = 
                    let rec go =                                     
                        function
                        | [] -> false
                        | MapEmpty :: rest -> go rest
                        | MapOne (k,v) :: rest -> 
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- rest
                            true                   
                        | (MapNode(k,v,l,r,_)) :: rest ->             
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- l :: r :: rest
                            true

                    go stack

                  member self.Reset() = stack <- mapList ()
            interface System.IDisposable with 
                  member self.Dispose() = stack <- [] }

    member __.toSeq2 () =
        let mutable stack = []
        let mutable index = 0
        let rec getStack(i) =
            if isEmpty bucket.[bucketIndex(i,bucketBitMask)].[shardIndex(i)] then
                if i < capacity then 
                    getStack(i+1)
                else
                    false
            else
                stack <- [ bucket.[bucketIndex(i,bucketBitMask)].[shardIndex(i)] ]
                index <- i + 1
                true                                                   
                    
        let mutable current = Unchecked.defaultof<KeyValuePair<_,_>>

        { new IEnumerator<_> with 
                member self.Current = current
            interface System.Collections.IEnumerator with
                  member self.Current = box self.Current
                  member self.MoveNext() = 
                    let rec go =                                     
                        function
                        | [] -> 
                            if index < capacity then
                                if getStack(index) then
                                    go stack
                                else
                                    false
                            else
                                false
                        | MapEmpty :: rest -> go rest
                        | MapOne (k,v) :: rest -> 
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- rest
                            true                   
                        | (MapNode(k,v,l,r,_)) :: rest ->             
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- l :: r :: rest
                            true

                    go stack

                  member self.Reset() = 
                                stack <- []
                                index <- 0
            interface System.IDisposable with 
                  member self.Dispose() = stack <- [] }

    

    member __.toSeq3 () =
        let mutable stack = []
        let mutable gbi = 0
        let mutable gsi = 0
        let inline canIncrSi si = si + 1 < ShardSize
        let inline canIncrBi bi = bi + 1 < bucket.Length
        let rec getStack(bi,si) =
            if isEmpty bucket.[bi].[si] then
                if canIncrSi si then getStack(bi,si + 1)
                elif canIncrBi bi then getStack(bi + 1,0)
                else
                    false
            else
                stack <- [ bucket.[bi].[si] ]
                if canIncrSi si then gbi <- bi ; gsi <- si + 1
                elif canIncrBi bi then gbi <- bi + 1 ; gsi <- 0
                else gbi <- -1
                true                                                   
                    
        let mutable current = Unchecked.defaultof<KeyValuePair<_,_>>

        { new IEnumerator<_> with 
                member self.Current = current
            interface System.Collections.IEnumerator with
                  member self.Current = box self.Current
                  member self.MoveNext() = 
                    let rec go =                                     
                        function
                        | [] -> 
                            if gbi <> -1 then
                                if getStack(gbi,gsi) then
                                    go stack
                                else
                                    false
                            else
                                false
                        | MapEmpty :: rest -> go rest
                        | MapOne (k,v) :: rest -> 
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- rest
                            true                   
                        | (MapNode(k,v,l,r,_)) :: rest ->             
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- l :: r :: rest
                            true

                    go stack

                  member self.Reset() = 
                                stack <- []
                                gbi <- 0
                                gsi <- 0
            interface System.IDisposable with 
                  member self.Dispose() = stack <- [] }              


    member __.toSeq4 () =
        let mutable stack = []
        let rec getStack(i) =
            if isEmpty bucket.[bucketIndex(i,bucketBitMask)].[shardIndex(i)] then
                if i < capacity then 
                    getStack(i+1)
            else
                stack <- bucket.[bucketIndex(i,bucketBitMask)].[shardIndex(i)] :: stack
                if i < capacity then 
                    getStack(i+1)
        
        getStack(0)                            
        let mutable current = Unchecked.defaultof<KeyValuePair<_,_>>

        { new IEnumerator<_> with 
                member self.Current = current
            interface System.Collections.IEnumerator with
                  member self.Current = box self.Current
                  member self.MoveNext() = 
                    let rec go =                                     
                        function
                        | [] -> false
                        | MapEmpty :: rest -> go rest
                        | MapOne (k,v) :: rest -> 
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- rest
                            true                   
                        | (MapNode(k,v,l,r,_)) :: rest ->             
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- l :: r :: rest
                            true

                    go stack

                  member self.Reset() = 
                                stack <- []
                                getStack(0)
            interface System.IDisposable with 
                  member self.Dispose() = stack <- [] }    


////////////////

    member __.Count = !countRef

    member __.BucketSize = bucket.Length

    member __.PrintLayout () =
        let mutable rowCount = 0
        let mutable tmapCount = 0
        let mutable rmapCount = 0
        let columnCount = Array.zeroCreate<int>(bucket.Length)
        printfn "Printing Layout:"
        for i in 0 .. bucket.Length - 1 do
            rowCount <- 0
            rmapCount <- 0

            printf "%4i {" i
            for j in 0 .. ShardSize - 1 do
                let m = bucket.[i].[j]
                if isEmpty m then
                    printf " ___ |"
                else
                    tmapCount <- tmapCount + 1
                    rmapCount <- rmapCount + 1
                    columnCount.[i] <- columnCount.[i] + (MapTree.size m)
                    rowCount <- rowCount + (MapTree.size m)
                    printf " %3i |" (MapTree.size m)
            printfn "} = %5i[%6i]" rmapCount rowCount
        
        printf "Total{" 
        for j in 0 .. ShardSize - 1 do
            printf " %3i |" columnCount.[j]
        printfn "} = %5i[%6i]" tmapCount !countRef            
    

    interface IEnumerable<KeyValuePair<'K, 'V>> with
        member s.GetEnumerator() = s.toSeq()

    interface System.Collections.IEnumerable with
        override s.GetEnumerator() = (s.toSeq() :> System.Collections.IEnumerator)

    member private __.getBucket () = bucket

    member __.Exists (fn:'K -> 'V -> bool) = exists fn

    member __.TryFindInRange fn = tryFindInRange fn

    member __.Merge (map:ShardMap<'K,'V>) : ShardMap<'K,'V> =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        
        let target, additions, tCount = // target will be a copy of the bigger of the two maps
            if map.BucketSize > bucket.Length then
                let target = Array.zeroCreate<Shard<'K,'V>>(map.BucketSize)
                Array.Copy(map.getBucket(),target,map.BucketSize)
                target, bucket, ref (map.Count)
            else
                let target = Array.zeroCreate<Shard<'K,'V>>(bucket.Length)
                Array.Copy(bucket,target,bucket.Length)
                target, map.getBucket() , ref (!countRef)
                
        let trgtBitDepth = calcBitMaskDepth ((target.Length * ShardSize) - 1)
        let bucketBitMask = calcSubBitMask trgtBitDepth
        
        let mapFn = 
            if additions.Length = target.Length then
                // Split into two types of mapping, one-to-one, and small map expansion
                ////////////////////////////////////////////////////////////////////////
                fun bi si sm ->
                    let tshrd = target.[bi]
                    let tm = tshrd.[si]
                    // Buckets same size so simple to one-to-one map
                    if isEmpty tm then
                        Interlocked.Add(tCount,MapTree.size sm) |> ignore
                        tshrd.[si] <- sm
                    else
                        tshrd.[si] <-
                            MapTree.fold (fun acc k v -> // for each key in source
                                MapTree.addAndIncr comparer k v tCount acc // lookup doubled so might be worth extending Maptree to return both tree & `newAddition' bool
                            ) tm sm
             else
                fun _ si sm ->
                    // Bucket lower order so shard needs to be remapped to higher order
                    ///////////////////////////////////////////////////////////////////////
                    MapTree.iter (fun k v -> // for each key in source
                        let kh = k.GetHashCode()
                        let tbi = bucketIndex(kh,bucketBitMask)
                        let tshrd = target.[tbi]
                        let tm = tshrd.[si]

                        if isEmpty tm then
                            Interlocked.Increment(tCount) |> ignore
                            tshrd.[si] <- MapOne(k,v)
                        else                                             
                            tshrd.[si] <- MapTree.addAndIncr comparer k v tCount tm
                    ) sm


        eachMapInBucket(additions , mapFn)
        // Step through maps to union
        ShardMap<'K,'V>(!tCount,target)

    member __.MergeMap (mapFn:'V -> 'T -> 'V) (mergeMap:ShardMap<'K,'T>) : ShardMap<'K,'V> =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        
        count
        let target, tCount = // target will be a copy of the bigger of the two maps
            if mergeMap.BucketSize > bucket.Length then
                let target = Array.zeroCreate<Shard<'K,'V>>(mergeMap.BucketSize)
                //Array.Copy(mergeMap.getBucket(),target,mergeMap.BucketSize)
                target, ref (mergeMap.Count)
            else
                let target = Array.zeroCreate<Shard<'K,'V>>(bucket.Length)
                //Array.Copy(bucket,target,bucket.Length)
                target,  ref (!countRef)
                
        let trgtBitDepth = calcBitMaskDepth ((target.Length * ShardSize) - 1)
        let bucketBitMask = calcSubBitMask trgtBitDepth
        
        let mapFn = 
            if additions.Length = target.Length then
                // Split into two types of mapping, one-to-one, and small map expansion
                ////////////////////////////////////////////////////////////////////////
                fun bi si sm ->
                    let tshrd = target.[bi]
                    let tm = tshrd.[si]
                    // Buckets same size so simple to one-to-one map
                    if isEmpty tm then
                        Interlocked.Add(tCount,MapTree.size sm) |> ignore
                        tshrd.[si] <- sm
                    else
                        tshrd.[si] <-
                            MapTree.fold (fun acc k v -> // for each key in source
                                MapTree.addAndIncr comparer k v tCount acc // lookup doubled so might be worth extending Maptree to return both tree & `newAddition' bool
                            ) tm sm
             else
                fun _ si sm ->
                    // Bucket lower order so shard needs to be remapped to higher order
                    ///////////////////////////////////////////////////////////////////////
                    MapTree.iter (fun k v -> // for each key in source
                        let kh = k.GetHashCode()
                        let tbi = bucketIndex(kh,bucketBitMask)
                        let tshrd = target.[tbi]
                        let tm = tshrd.[si]

                        if isEmpty tm then
                            Interlocked.Increment(tCount) |> ignore
                            tshrd.[si] <- MapOne(k,v)
                        else                                             
                            tshrd.[si] <- MapTree.addAndIncr comparer k v tCount tm
                    ) sm


        eachMapInBucket(additions , mapFn)
        // Step through maps to union
        ShardMap<'K,'V>(!tCount,target)

    //////////////////////////
    /////////////////////////////////////
    static member Union (unionf:seq<'V> -> 'T) (maps:ShardMap<'K,'V> seq) : ShardMap<'K,'T> =        
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>

        let processMaps (unionf:seq<'V> -> 'T,sources:ShardMap<'K,'V> seq) =
            //let mutable target = Unchecked.defaultof<Bucket<'K,MutateHead<'V>>>
            let enum = sources.GetEnumerator()
            let tCount = ref 0 

            let rec go(source:Bucket<'K,'V>,target:Bucket<'K,MutateHead<'V>>) =
                if source.Length = target.Length then
                    Tasks.Parallel.For(0,source.Length,fun bi ->
                        let sshrd = source.[bi]
                        
                        let mutable tshrd = target.[bi]// target.[bi] << target shard depends on bitdepth

                        for si in 0 .. ShardSize - 1 do
                            let sm = sshrd.[si]
                            if isEmpty sm |> not then
                                let mutable tm = tshrd.[si] //<< target shard depends on bitdepth
                                if isEmpty tm then
                                    tCount := Interlocked.Add(tCount,MapTree.size sm)
                                    tshrd.[si] <- MapTree.map (fun v -> MutateHead<_>(v)) sm
                                else
                                    tshrd.[si] <-
                                        MapTree.fold (fun acc k v -> // for each key in source
                                            match MapTree.tryFind comparer k acc with // try find in acc target
                                            | Some mh -> 
                                                mh.Add v
                                                acc
                                            | None -> 
                                                tCount := Interlocked.Increment(tCount)
                                                MapTree.add comparer k (MutateHead<'V>(v)) acc
                                        ) tm sm
                    ) |> ignore    
                if enum.MoveNext() then
                    go(enum.Current.getBucket(),target)
                else
                    //end of list so map value lists to new dictionary with provided unionf
                    enum.Dispose()
                    ShardMap.transpose (MapTree.map (fun (mh:MutateHead<'V>) -> unionf mh.Head )) !tCount target
            
            // start of enumeration (first shard used to create target interim map)
            if enum.MoveNext() then
                let ibucket = enum.Current.getBucket()
                let target = Array.zeroCreate<Shard<'K,MutateHead<'V>>>(ibucket.Length)
                for bi in 0 .. ibucket.Length - 1 do
                    target.[bi] <- Array.zeroCreate<MapTree<'K,MutateHead<'V>>>(ShardSize)
                go(ibucket,target)
            else
                enum.Dispose()
                ShardMap<'K,'T>(0,[])
    
        processMaps(unionf,maps)  //<<HACK to get intellisense to work


    static member Union2 (unionf:seq<'V> -> 'T) (maps:ShardMap<'K,'V> seq) : ShardMap<'K,'T> =        
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>

        let processMaps (unionf:seq<'V> -> 'T,sources:ShardMap<'K,'V> seq) =
            //let mutable target = Unchecked.defaultof<Bucket<'K,MutateHead<'V>>>
            let enum = sources.GetEnumerator()
            let tCount = ref 0 

            let rec go(source:ShardMap<'K,'V>,target:ShardMap<'K,MutateHead<'V>>) =
                let ntarget =                
                    source.Fold (fun (trgt:ShardMap<'K,MutateHead<'V>>) k v ->
                        match trgt.TryFind k with
                        | Some mh -> 
                            mh.Add v
                            trgt
                        | None -> 
                            tCount := Interlocked.Increment(tCount)
                            trgt.Add (k,MutateHead<'V>(v))
                            trgt
                    ) target 

                if enum.MoveNext() then
                    go(enum.Current,ntarget)
                else
                    //end of list so map value lists to new dictionary with provided unionf
                    enum.Dispose()
                    ntarget.Map (fun (mh:MutateHead<'V>) -> unionf mh.Head )
            
            // start of enumeration (first shard used to create target interim map)
            if enum.MoveNext() then
                let ibucket = enum.Current.getBucket()
                let targetBucket = Array.zeroCreate<Shard<'K,MutateHead<'V>>>(ibucket.Length)
                go(enum.Current,ShardMap<_,_>(0,targetBucket))
            else
                enum.Dispose()
                ShardMap<'K,'T>(0,[])

            
        
        processMaps(unionf,maps)  //<<HACK to get intellisense to work

    static member UnionSingle (unionf:seq<'V> -> 'T) (maps:ShardMap<'K,'V> seq) : ShardMap<'K,'T> =        
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>

        let processMaps (unionf:seq<'V> -> 'T,sources:ShardMap<'K,'V> seq) =
            //let mutable target = Unchecked.defaultof<Bucket<'K,MutateHead<'V>>>
            let enum = sources.GetEnumerator()
            let tCount = ref 0 

            let rec go(source:Bucket<'K,'V>,target:Bucket<'K,MutateHead<'V>>) =
                 
                for bi in 0 .. source.Length - 1 do
                        let sshrd = source.[bi]
                        
                        let mutable tshrd = target.[bi]// target.[bi] << target shard depends on bitdepth

                        for si in 0 .. ShardSize - 1 do
                            let sm = sshrd.[si]
                            if isEmpty sm |> not then
                                let mutable tm = tshrd.[si] //<< target shard depends on bitdepth
                                if isEmpty tm then
                                    tCount := Interlocked.Add(tCount,MapTree.size sm)
                                    tshrd.[si] <- MapTree.map (fun v -> MutateHead<_>(v)) sm
                                else
                                    tshrd.[si] <-
                                        MapTree.fold (fun acc k v -> // for each key in source
                                            match MapTree.tryFind comparer k acc with // try find in acc target
                                            | Some mh -> 
                                                mh.Add v
                                                acc
                                            | None -> 
                                                tCount := Interlocked.Increment(tCount)
                                                MapTree.add comparer k (MutateHead<'V>(v)) acc
                                        ) tm sm  

                if enum.MoveNext() then
                    go(enum.Current.getBucket(),target)
                else
                    //end of list so map value lists to new dictionary with provided unionf
                    enum.Dispose()
                    //let tshard = ShardMap<_,_>(!tCount,target)
                    let fbucket = Array.zeroCreate<Shard<'K,'T>>(target.Length)
                    for fi in 0 .. fbucket.Length - 1 do
                        fbucket.[fi] <- Array.zeroCreate<MapTree<'K,'T>>(ShardSize)

                    for bi in 0 .. target.Length - 1 do
                        
                        let tshrd = target.[bi]// target.[bi] << target shard depends on bitdepth
                        let fshrd = fbucket.[bi]
                        for si in 0 .. ShardSize - 1 do
                            let tm = tshrd.[si]
                            if isEmpty tm |> not then
                                fshrd.[si] <- MapTree.map (fun (mh:MutateHead<'V>) -> unionf mh.Head ) tm
                    ShardMap(!tCount,fbucket)
            
            // start of enumeration (first shard used to create target interim map)
            if enum.MoveNext() then
                let ibucket = enum.Current.getBucket()
                let target = Array.zeroCreate<Shard<'K,MutateHead<'V>>>(ibucket.Length)
                for bi in 0 .. ibucket.Length - 1 do
                    target.[bi] <- Array.zeroCreate<MapTree<'K,MutateHead<'V>>>(ShardSize)
                go(enum.Current.getBucket(),target)
            else
                enum.Dispose()
                ShardMap<'K,'T>(0,[])

            
        
        processMaps(unionf,maps)  //<<HACK to get intellisense to work


    static member UnionList (unionf:'V list -> 'T) (maps:ShardMap<'K,'V> list) : ShardMap<'K,'T> =        
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>

        let processMaps (unionf:list<'V> -> 'T,sources:ShardMap<'K,'V> seq) =
            let tCount = ref 0 

            let rec go(source:Bucket<'K,'V>,target:Bucket<'K,MutateHead<'V>>,tail:ShardMap<'K,'V> list) =
                if source.Length = target.Length then
                    Tasks.Parallel.For(0,source.Length,fun bi ->
                        let sshrd = source.[bi]
                        
                        let mutable tshrd = target.[bi]// target.[bi] << target shard depends on bitdepth

                        for si in 0 .. ShardSize - 1 do
                            let sm = sshrd.[si]
                            if isEmpty sm |> not then
                                let mutable tm = tshrd.[si] //<< target shard depends on bitdepth
                                if isEmpty tm then
                                    tCount := Interlocked.Add(tCount,MapTree.size sm)
                                    tshrd.[si] <- MapTree.map (fun v -> MutateHead<_>(v)) sm
                                else
                                    tshrd.[si] <-
                                        MapTree.fold (fun acc k v -> // for each key in source
                                            match MapTree.tryFind comparer k acc with // try find in acc target
                                            | Some mh -> 
                                                mh.Add v
                                                acc
                                            | None -> 
                                                tCount := Interlocked.Increment(tCount)
                                                MapTree.add comparer k (MutateHead<'V>(v)) acc
                                        ) tm sm
                    ) |> ignore
                match tail with                   
                | [] -> ShardMap.transpose (MapTree.map (fun (mh:MutateHead<'V>) -> unionf mh.Head )) !tCount target
                | h :: t -> go(h.getBucket(),target,t)

            
            // start of enumeration (first shard used to create target interim map)
            match maps with
            | [] -> ShardMap<'K,'T>(0,[])
            | h :: t ->
                let ibucket = h.getBucket()
                let target = Array.zeroCreate<Shard<'K,MutateHead<'V>>>(ibucket.Length)
                for bi in 0 .. ibucket.Length - 1 do
                    target.[bi] <- Array.zeroCreate<MapTree<'K,MutateHead<'V>>>(ShardSize)
                go(ibucket,target,t)
        
        processMaps(unionf,maps)  //<<HACK to get intellisense to work

    static member UnionParallel (unionf:'V list -> 'T) (maps:ShardMap<'K,'V> list) : ShardMap<'K,'T> =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let tCount = ref 0 

        let threadBuckets(sources:Bucket<'K,'V> list,target:Bucket<'K,MutateHead<'V>>) =
            let fBucket = Array.zeroCreate<Shard<'K,'T>>(target.Length)
            let trgtBitDepth = calcBitMaskDepth ((target.Length * ShardSize) - 1)
            let bucketBitMask = calcSubBitMask trgtBitDepth

            let mapSameSize =
                fun bi si sm ->
                    let tshrd = getOrCreateShard(target,bi)
                    let tm = tshrd.[si]
                    // Buckets same size so simple to one-to-one map
                    if isEmpty tm then
                        Interlocked.Add(tCount,MapTree.size sm) |> ignore
                        tshrd.[si] <- MapTree.map (fun v -> MutateHead<_>(v)) sm
                    else
                        tshrd.[si] <-
                            MapTree.fold (fun acc k v -> // for each key in source
                                match MapTree.tryFind comparer k acc with // try find in acc target
                                | Some mh -> 
                                    mh.Add v
                                    acc
                                | None -> 
                                    Interlocked.Increment(tCount) |> ignore
                                    MapTree.add comparer k (MutateHead<'V>(v)) acc
                            ) tm sm

            let mapUpSize =
                fun _ si sm ->
                    MapTree.iter (fun k v -> // for each key in source
                        let kh = k.GetHashCode()
                        let tbi = bucketIndex(kh,bucketBitMask)
                        let tshrd = getOrCreateShard(target,tbi)
                        let tm = tshrd.[si]
                        if isEmpty tm then
                            Interlocked.Increment(tCount) |> ignore
                            tshrd.[si] <- MapOne(k,MutateHead<'V>(v))
                        else                                             
                            match MapTree.tryFind comparer k tm with // try find in acc target
                            | Some mh ->
                                mh.Add v
                            | None -> 
                                Interlocked.Increment(tCount) |> ignore
                                tshrd.[si] <-
                                    MapTree.add comparer k (MutateHead<'V>(v)) tm
                    ) sm  

            let rec go (ls:Bucket<'K,'V> list) = 
                match ls with
                | [] ->
                    // Apply unionF
                    Tasks.Parallel.For(0,target.Length,fun bi ->
                        fBucket.[bi] <- Array.zeroCreate<_>(ShardSize)
                        // mapping of final shard from target to final
                        let tshrd = target.[bi]
                        let fshrd = fBucket.[bi]
                        for si in 0 .. ShardSize - 1 do
                            let tm = tshrd.[si]
                            if isEmpty tm |> not then   
                                fshrd.[si] <- MapTree.map (fun (mh:MutateHead<'V>) -> unionf mh.Head) tm          
                    ) |> ignore
                | h :: t -> 
                    let mapFn = if h.Length = target.Length then mapSameSize else mapUpSize
                    // Step through maps to union
                    eachMapInBucket(h, mapFn)
                    // rec go to next bucket on list
                    go(t)
            // begin processing list
            go(sources)

            ShardMap<'K,'T>(!tCount,fBucket)
        
        // start of enumeration (first shard used to create target interim map)
        let maxBucket, buckets = maps |> List.fold (fun (mb,bl) m -> (if m.BucketSize > mb then m.BucketSize else mb) , m.getBucket() :: bl ) (0,[])
        let target = Array.zeroCreate<Shard<'K,MutateHead<'V>>>(maxBucket)
        threadBuckets(buckets ,target)


    static member UnionParaParallel (unionf:'V list -> 'T) (maps:ShardMap<'K,'V> list) : ShardMap<'K,'T> =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let tCount = ref 0 
        let coreShift = (calcBitMaskDepth Environment.ProcessorCount) - 1

        let threadBuckets(sources:Bucket<'K,'V> list,target:Bucket<'K,MutateHead<'V>>) =
            let fBucket = Array.zeroCreate<Shard<'K,'T>>(target.Length)
            let trgtBitDepth = calcBitMaskDepth ((target.Length * ShardSize) - 1)
            let bucketBitMask = calcSubBitMask trgtBitDepth


            let rec go (ls:Bucket<'K,'V> list) = 
                match ls with
                | [] -> ()
                                      
                | h :: t -> 

                    Tasks.Parallel.For(0,h.Length >>> coreShift,fun pi ->
                        
                        for bi in pi <<< coreShift .. ((pi + 1) <<< coreShift) - 1 do
                        // adding each value in maps to placeholder node before compute                                 
                            let sshrd = h.[bi]
                            // itterate through shards
                            for si in 0 .. ShardSize - 1 do
                                let sm = sshrd.[si]
                                if isEmpty sm |> not then
                                    // Split into two types of mapping, one-to-one, and small map expansion
                                    ////////////////////////////////////////////////////////////////////////
                                    if h.Length = target.Length then
                                        
                                        let mutable tshrd = target.[bi]
                                        if isEmpty tshrd then 
                                            let ntshrd = Array.zeroCreate<MapTree<'K,MutateHead<'V>>>(ShardSize)
                                            target.[bi] <- tshrd
                                            tshrd <- tshrd

                                        let tm = tshrd.[si]
                                        // Buckets same size so simple to one-to-one map
                                        if isEmpty tm then
                                            tCount := Interlocked.Add(tCount,MapTree.size sm)
                                            tshrd.[si] <- MapTree.map (fun v -> MutateHead<_>(v)) sm
                                        else
                                            tshrd.[si] <-
                                                MapTree.fold (fun acc k v -> // for each key in source
                                                    match MapTree.tryFind comparer k acc with // try find in acc target
                                                    | Some mh -> 
                                                        mh.Add v
                                                        acc
                                                    | None -> 
                                                        tCount := Interlocked.Increment(tCount)
                                                        MapTree.add comparer k (MutateHead<'V>(v)) acc
                                                ) tm sm
                                    else
                                        // Bucket lower order so shard needs to be remapped with higher order
                                        ///////////////////////////////////////////////////////////////////////
                                        MapTree.iter (fun k v -> // for each key in source
                                            let kh = k.GetHashCode()
                                            let tbi = bucketIndex(kh,bucketBitMask)
                                            let tshrd = target.[tbi]
                                            if isEmpty tshrd then
                                                target.[tbi] <- Array.zeroCreate<MapTree<'K,MutateHead<'V>>>(ShardSize)
                                            let tm = target.[tbi].[si]

                                            if isEmpty tm then
                                                tCount := Interlocked.Increment(tCount)
                                                target.[tbi].[si] <- MapOne(k,MutateHead<'V>(v))
                                            else                                             
                                                match MapTree.tryFind comparer k tm with // try find in acc target
                                                | Some mh ->
                                                    mh.Add v
                                                | None -> 
                                                    tCount := Interlocked.Increment(tCount)
                                                    target.[tbi].[si] <-
                                                        MapTree.add comparer k (MutateHead<'V>(v)) tm
                                        ) sm                                     

                        
                    ) |> ignore
                    // next bucket on list
                    go(t)
            // begin processing list
            go(sources)
            
            // Apply unionF
            Tasks.Parallel.For(0,target.Length,fun bi ->
                fBucket.[bi] <- Array.zeroCreate<_>(ShardSize)
                // mapping of final shard from target to final
                let tshrd = target.[bi]
                let fshrd = fBucket.[bi]
                for si in 0 .. ShardSize - 1 do
                    let tm = tshrd.[si]
                    if isEmpty tm |> not then   
                        fshrd.[si] <- MapTree.map (fun (mh:MutateHead<'V>) -> unionf mh.Head) tm          
            ) |> ignore

            ShardMap<'K,'T>(!tCount,fBucket)

        // start of enumeration (first shard used to create target interim map)
        let maxBucket, buckets = maps |> List.fold (fun (mb,bl) m -> (if m.BucketSize > mb then m.BucketSize else mb) , m.getBucket() :: bl ) (0,[])
        let target = Array.zeroCreate<Shard<'K,MutateHead<'V>>>(maxBucket)
        threadBuckets(buckets ,target)

    static member UnionParallelWrong (unionf:'V list -> 'T) (maps:ShardMap<'K,'V> list) : ShardMap<'K,'T> =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let tCount = ref 0 

        let threadBuckets(sources:Bucket<'K,'V> list,target:Bucket<'K,MutateHead<'V>>) =
            let fBucket = Array.zeroCreate<Shard<'K,'T>>(target.Length)
            let trgtBitDepth = calcBitMaskDepth ((target.Length * ShardSize) - 1)
            let bucketBitMask = calcSubBitMask trgtBitDepth

            Tasks.Parallel.For(0,target.Length,fun bi ->
                if isEmpty target.[bi] then target.[bi] <- Array.zeroCreate<MapTree<'K,MutateHead<'V>>>(ShardSize)
                fBucket.[bi] <- Array.zeroCreate<_>(ShardSize)   
                
                let rec go (ls:Bucket<'K,'V> list) = 
                    match ls with
                    | [] ->
                        // mapping of final shard from target to final
                        let tshrd = target.[bi]
                        let fshrd = fBucket.[bi]
                        for si in 0 .. ShardSize - 1 do
                            let tm = tshrd.[si]
                            if isEmpty tm |> not then
                                //HACK
                                //MapTree.iter (fun k (v:MutateHead<'V>) -> if v.Head.Length > 4 then printfn ">4: %A >> %A" k v.Head ) tm
                                    
                                fshrd.[si] <- MapTree.map (fun (mh:MutateHead<'V>) -> unionf mh.Head) tm                            
                    | h :: t -> 
                        // adding each value in maps to placeholder node before compute 
                        if bi < h.Length then
                            
                            let sshrd = h.[bi]
                            // itterate through shards
                            for si in 0 .. ShardSize - 1 do
                                let sm = sshrd.[si]
                                if isEmpty sm |> not then
                                    // Split into two types of mapping, one-to-one, and small map expansion
                                    if h.Length = target.Length then
                                        let tshrd = target.[bi]
                                        let tm = tshrd.[si]
                                        // Buckets same size so simple to one-to-one map
                                        if isEmpty tm then
                                            tCount := Interlocked.Add(tCount,MapTree.size sm)
                                            tshrd.[si] <- MapTree.map (fun v -> MutateHead<_>(v)) sm
                                        else
                                            tshrd.[si] <-
                                                MapTree.fold (fun acc k v -> // for each key in source
                                                    match MapTree.tryFind comparer k acc with // try find in acc target
                                                    | Some mh -> 
                                                        mh.Add v
                                                        acc
                                                    | None -> 
                                                        tCount := Interlocked.Increment(tCount)
                                                        MapTree.add comparer k (MutateHead<'V>(v)) acc
                                                ) tm sm
                                    else
                                        // Bucket lower order so shard needs to be remapped with higher order
                                        MapTree.iter (fun k v -> // for each key in source
                                            let kh = k.GetHashCode()
                                            let tbi = bucketIndex(kh,bucketBitMask)
                                            let tshrd = target.[tbi]
                                            if isEmpty tshrd then
                                                 target.[tbi] <- Array.zeroCreate<MapTree<'K,MutateHead<'V>>>(ShardSize)
                                            let tm = target.[tbi].[si]

                                            if isEmpty tm then
                                                tCount := Interlocked.Increment(tCount)
                                                target.[tbi].[si] <- MapOne(k,MutateHead<'V>(v))
                                            else                                             
                                                match MapTree.tryFind comparer k tm with // try find in acc target
                                                | Some mh ->
                                                    mh.Add v
                                                | None -> 
                                                    tCount := Interlocked.Increment(tCount)
                                                    target.[tbi].[si] <-
                                                        MapTree.add comparer k (MutateHead<'V>(v)) tm
                                        ) sm                                     
                        // next bucket on list
                        go(t)
                // begin processing list
                go(sources)
                
            ) |> ignore

            ShardMap<'K,'T>(!tCount,fBucket)
        
        // start of enumeration (first shard used to create target interim map)
        let maxBucket, buckets = maps |> List.fold (fun (mb,bl) m -> (if m.BucketSize > mb then m.BucketSize else mb) , m.getBucket() :: bl ) (0,[])
        let target = Array.zeroCreate<Shard<'K,MutateHead<'V>>>(maxBucket)
        threadBuckets(buckets ,target)

    ////////////////////////////////////
    /// Contructors
    ///////////////////////////////////

    new(counter:int,items:('K * 'V) seq) =
        let size = if counter < ShardSize then ShardSize else counter
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let bitdepth = (calcBitMaskDepth size)
        let bucketSize = pow2 (bitdepth)
        let bucketBitMask = calcSubBitMask bitdepth
        let newBucket = Array.zeroCreate<Shard<'K,'V>>(bucketSize)

        items
        |> Seq.iter (fun (k,v) -> 
            let kh = k.GetHashCode()
            let bi = bucketIndex(kh,bucketBitMask)
            let shrd = getOrCreateShard(newBucket,bi)
            let si = shardIndex(kh)
            let m = shrd.[si]
            shrd.[si] <- 
                if isEmpty m then
                    //printfn "$| creating new map for key:'%A' [%i][%i] for value:%A" k bi si v
                    MapOne (k,v)
                else
                    //printfn "+| adding key:'%A' [%i][%i] for value:%A to map {%A}" k bi si v m
                    MapTree.add comparer k v m                        
            )
        //now allocate any empties that were not filled
        
        ShardMap<'K,'V>(counter,newBucket)

    new(counter:int,items:'V seq,keyFn:'V -> 'K) =
        let size = if counter < ShardSize then ShardSize else counter
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let bitdepth = (calcBitMaskDepth size)
        let bucketSize = pow2 (bitdepth)
        let bucketBitMask = calcSubBitMask bitdepth
        let newBucket = Array.zeroCreate<Shard<'K,'V>>(bucketSize)

        items
        |> Seq.iter (fun v ->
            let k = keyFn v
            let kh = k.GetHashCode()
            let bi = bucketIndex(kh,bucketBitMask)
            let shrd = getOrCreateShard(newBucket,bi)
            let si = shardIndex(kh)
            let m = shrd.[si]
            shrd.[si] <- 
                if isEmpty m then
                    //printfn "$| creating new map for key:'%A' [%i][%i] for value:%A" k bi si v
                    MapOne (k,v)
                else
                    //printfn "+| adding key:'%A' [%i][%i] for value:%A to map {%A}" k bi si v m
                    MapTree.add comparer k v m                        
            )
        //now allocate any empties that were not filled
        
        ShardMap<'K,'V>(counter,newBucket)

    new(kvps:'V seq,keyFn:'V -> 'K) =       
        let mutable counter = 0
        let mutable items = []
        kvps |> Seq.iter (fun kvp -> 
            counter <- counter + 1
            items <- kvp :: items
        )
        ShardMap<_,_>(counter,items,keyFn)

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
type NameMap<'T> = ShardMap<string,'T>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module NameMap =
    let empty<'T> = NameMap<'T>(0,[])
    let range (m:NameMap<'T>) = List.rev (m.FoldBack (fun _ x acc -> x :: acc) [])
    [<Obsolete("Warning: fold & foldback executed in no particular order, use Map<'Key,'T> if ordering needed")>]
    let foldBack f (m:NameMap<'T>) z = m.FoldBack f z
    let forall f (m:NameMap<'T>) = m.FoldBack (fun x y acc -> acc && f x y)  true
    let exists f (m:NameMap<'T>) = m.Exists f
    let ofKeyedList f l = NameMap<'T>(List.length l,l,f)
    let ofList l : NameMap<'T> = NameMap<'T>(l)
    let ofSeq l : NameMap<'T> = NameMap<'T>(l)
    let toList (l: NameMap<'T>) = l.Fold (fun acc k v -> (k,v) :: acc ) []
    let layer (m1 : NameMap<'T>) m2 = m1.Merge m2

    /// Not a very useful function - only called in one place - should be changed 
    let layerAdditive addf (m1:NameMap<'T>) (m2:NameMap<'T>) = 
      //m2.Fold (fun x y sofar -> Map.add x (addf (Map.tryFindMulti x sofar) y))

      Map.foldBack (fun x y sofar -> Map.add x (addf (Map.tryFindMulti x sofar) y) sofar) m1 m2

    /// Union entries by identical key, using the provided function to union sets of values
    let union unionf (ms: NameMap<_> list) = NameMap.UnionParallel unionf ms
        
    /// For every entry in m2 find an entry in m1 and fold 
    let subfold2 errf f (m1:NameMap<_>) (m2:NameMap<_>) acc =
        m2.FoldBack (fun n x2 acc -> match m1.TryFind n with | Some v1 -> f n v1 x2 acc | None -> errf n x2 ) acc
        
    let suball2 errf p m1 m2 = subfold2 errf (fun _ x1 x2 acc -> p x1 x2 && acc) m1 m2 true

    let mapFold f s (l: NameMap<'T>) = 
        l.FoldBack (fun x y (l':NameMap<'T>,s') -> let y',s'' = f x y s' in l'.Add(x,y'); l' ,s'') (empty<'T>,s)

    let foldBackRange f (l: NameMap<'T>) acc = l.FoldBack (fun _ y acc -> f y acc) acc

    let filterRange f (l: NameMap<'T>) = l.FoldBack (fun x y (acc:NameMap<'T>) -> if f y then acc.Add(x,y); acc else acc) empty<'T>

    let mapFilter f (l: NameMap<'T>) = l.FoldBack (fun x y (acc:NameMap<'T>) -> match f y with None -> acc | Some y' -> acc.Add(x, y');acc ) empty<'T>

    let map f (l : NameMap<'T>) = l.Map f

    let iter f (l : NameMap<'T>) = l.Iter f

    let partition f (l : NameMap<'T>) = l.Partition f

    let mem v (m: NameMap<'T>) = m.ContainsKey v

    let find v (m: NameMap<'T>) = m.[v]

    let tryFind v (m: NameMap<'T>) = m.TryFind v  

    let add v x (m: NameMap<'T>) = m.Add(v,x) ; m

    let isEmpty (m: NameMap<'T>) = (m.Count = 0)

    let existsInRange p (m: NameMap<'T>) = m.Exists (fun _ v -> p v)

    let tryFindInRange p (m: NameMap<'T>) = m.TryFindInRange p

let bprint (value:int) = System.Convert.ToString(value, 2).PadLeft(32, '0')

let bsprint (value:uint16) =  System.Convert.ToString(int value, 2).PadLeft(16, '0')

1us <<< 15
let left1 = 32768us
left1 >>> 4 |> bsprint

let addbitPos (state:uint16,pos:int) =
    (1us <<< pos) ||| state |> int |> bprint

let s = addbitPos(0us,7) 

GC.Collect()
let imem = GC.GetTotalMemory true

let amem = GC.GetTotalMemory true

GC.Collect()
let beforemem = GC.GetTotalMemory true
let smap = new ShardMap<_,_>(numberStrings)
let aftermem = GC.GetTotalMemory true

let nmap = smap.Map int
nmap.["98549420"]
//    ("98549420","1618963");
for _ in 0 .. 1000 do smap.TryFindInRange (fun v -> v = "8315119") |> ignore

#time
for i in  0 .. 10000 do
    let ml = smap.MapList
    ()

Tasks.Parallel.For(0,sample2.Length, fun i ->
    smap.Add sample2.[i]
    let k,_ = numberStrings.[i] 
    smap.[k] |> ignore
)

sample2.Length

for (k,v) in sample2 do
    smap.Add(k,v)

#time
let smap = new ShardMap<_,_>(bigData)

smap1.GetHashCode()
let smap1 = smap.AddToNew("alkdfjas","fadfdf")

let nsmap = ShardMap<int,string>([(1,"one");(2,"two");(3,"three")])
nsmap.BucketSize
nsmap.Count
nsmap.[2]

GC.Collect()
let beforemem = GC.GetTotalMemory true
let bmap = Map<_,_>(numberStrings)
let aftermem = GC.GetTotalMemory true


for i in 0 .. 1000 do
    let nsmap = smap.Map int
    ()

for i in 0 .. 1000 do
    let nbmap = Map.map (fun _ v -> int v) bmap
    ()
////////////////////////////////////////

for i in 0 .. 100000 do
    let nsmap = smap.Fold (fun acc _ _ -> acc + 1) 0 
    ()

for i in 0 .. 100000 do
    let nsmap = smap.Fold2 (fun acc _ _ -> acc + 1) 0
    ()

for i in 0 .. 100000 do
    let nbmap = Map.fold (fun acc _ _ -> acc + 1 ) 0 bmap
    ()

#time

smap.BucketSize
smap.Count
smap |> Seq.length
smap.PrintLayout()

calcBitMaskDepth smap.Count
List.length sml

2 <<< (11-5)

GC.Collect()
let mem3 = GC.GetTotalMemory true
let dict = Dictionary<string,string>()
for (k,v) in numberStrings do
    dict.Add(k,v)
let mem4 = GC.GetTotalMemory true

for (k,v) in sample2 do
    dict.Add(k,v)

dict.Count

//////////////
for i in 0 .. 10000 do
    let bmap = Map<_,_>(numberStrings)
    ()

for i in 0 .. 10000 do
    let smap = new ShardMap<_,_>(numberStrings)
    ()

///////////////
let lookuploops = 10000
#time
for i in 0 .. lookuploops do
    for (k,v) in numberStrings do
        if smap.[k] <> v then printfn "ERROR ON KEY MATCH: %A" k

for i in 0 .. lookuploops do
    for (k,v) in sample2 do
        if smap.[k] <> v then printfn "ERROR ON KEY MATCH: %A" k
////////////////////////////////////

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
let ittrLoops = 100000

let mutable counter = 0
printfn "coutner:%i" counter

#time
GC.Collect()
let beforemem = GC.GetTotalMemory true
for i in 0 .. ittrLoops do
    smap |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        // counter <- counter + 1
        ()
    )
GC.Collect()
let aftermem = GC.GetTotalMemory true

smap.toSeq ()

for i in 0 .. ittrLoops do
    bmap |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        // counter <- counter + 1
        ()
    ) 

for i in 0 .. ittrLoops do
    dict |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        //counter <- counter + 1
        ()
    )
#time
let ittr (enum:IEnumerator<_>) =
    while enum.MoveNext() do ()
    enum.Dispose()

//// differnt sequence methods
for _ in 0 .. 100000 do smap.toSeq()  |> ittr
for _ in 0 .. 100000 do smap.toSeq2() |> ittr 
for _ in 0 .. 100000 do smap.toSeq3() |> ittr 
for _ in 0 .. 100000 do smap.toSeq4() |> ittr 


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

smap.Fold (fun k v (str,i) -> (v.Substring(0,1) + str,i+1)) ("",0)

calcBitMaskDepth 47 |> bprint
higherRange(36,5) |> bprint
36 |> bprint

for i in 0 .. 10 do
    let k,_ = sample2.[i]
    let hk = k.GetHashCode()
    let bmd = 10
    let sft = ((hk >>> bmd + 1) &&& 0b1)
    let subBitMask = calcSubBitMask bmd    
    let si = hk &&& 0b1111
    let bi = (hk &&& subBitMask) >>> 4
    let sib = (bprint si).Substring(28,4)
    let bib = (bprint bi).Substring(32 - bmd + 4,bmd - 4)
    let hkb = bprint hk
    let sftb = sft = 1
    printfn "%A:hk{%11i} sft{%i} hk{%s} msk{%s} si{%3i:%s} bi{%3i:%s} >%b" k hk sft hkb (hkb.Substring(hkb.Length - bmd - 2,bmd + 1)) si sib bi bib sftb


let higherRange (index:int,bitdepth:int) = (index ||| (1 <<< (bitdepth - 4)))
higherRange(43,10) |> bprint

let v = 0b00001
let short (sft:int) = 1s <<< sft
short 3
let print16 (srt:int16)  = System.Convert.ToString(srt,2)
short 15 |> print16


let union unionf (ms: Map<string,_> seq) = 
    seq { for m in ms do yield! m } 
       |> Seq.groupBy (fun (KeyValue(k,_v)) -> k) 
       |> Seq.map (fun (k,es) -> (k,unionf (Seq.map (fun (KeyValue(_k,v)) -> v) es))) 
       |> Map.ofSeq

#time


let u1 = ShardMap<_,_>(union1)
let u2 = ShardMap<_,_>(union2)
let u3 = ShardMap<_,_>(union3)
let u4 = ShardMap<_,_>(union4)

let b1 = Map<_,_>(union1)
let b2 = Map<_,_>(union2)
let b3 = Map<_,_>(union3)
let b4 = Map<_,_>(union4)

#time
for i in 0 .. 10000 do
    let umap = [u1;u2;u3;u4] |> ShardMap.Union (Seq.sum)
    ()

for i in 0 .. 10000 do
    let umap = [u1;u2;u3;u4] |> ShardMap.Union2 (Seq.sum)
    ()

for i in 0 .. 10000 do
    let umap = [u1;u2;u3;u4] |> ShardMap.UnionSingle (Seq.sum)
    ()

for i in 0 .. 10000 do
    let umap2 = [u1;u2;u3;u4] |> ShardMap.UnionParallel (List.sum)
    ()

for i in 0 .. 10000 do
    let umap2 = [u1;u2;u3;u4] |> ShardMap.UnionParaPartition (List.sum)
    ()

for i in 0 .. 10000 do
    let umap = [u1;u2;u3;u4] |> ShardMap.UnionList (List.sum)
    ()

for i in 0 .. 10000 do
    let bumap = [b1;b2;b3;b4] |> union (Seq.sum)
    ()

let umap = [u1;u2;u3;u4] |> ShardMap.Union (Seq.sum)
let umap2 = [u1;u2;u3;u4] |> ShardMap.UnionParallel (List.sum)
umap.Fold (fun s _ v -> s + v) 0

for kvp in umap2 do
    printfn "%s = %i" kvp.Key kvp.Value

//////////////////////////////
/// merge / layering perf test
#time
let smu1 = ShardMap<_,_>(union1)
let smu2 = ShardMap<_,_>(union2)
for _ in 0 ..10000 do smu1.Merge(smu2) |> ignore
smu12.Count
let bmu1 = Map<_,_>(union1)
let bmu2 = Map<_,_>(union2)
for _ in 0 .. 10000 do Map.foldBack Map.add bmu1 bmu2 |> ignore

umap2.Count
Environment.ProcessorCount
let tmh = MutateHead<int>(1)
tmh.Add 2
tmh.Add 2
tmh.Add 4
tmh.Head

let bsprint (value:uint16) =  System.Convert.ToString(int value, 2).PadLeft(16, '0')
let left1 = 32768us
left1 >>> 1 |> bsprint

let addbitPos (state:uint16,pos:int) =
    (1us <<< pos) ||| state |> bsprint

let empty = MutateHead<int>(1)
let bucket = Array.zeroCreate<MutateHead<int>>(16)

let mutable posMask = 0us
let positions = [4;9;12;15]
for i in positions do
    bucket.[i] <- empty
    posMask <- (left1 >>> i) ||| posMask

bsprint posMask

let posMaskSearch () = 
    let rec go (i,acc) =
        if i < 16 then
            if ((left1 >>> i) &&& posMask) <> 0us then 
                go(i + 1,bucket.[i] :: acc)
            else
                go(i + 1,acc)
        else
            acc
    go(0,[])        

let itterSearch () =
    let mutable result = []
    for i in 0 .. bucket.Length - 1 do
        let v = bucket.[i]
        if Object.ReferenceEquals(null,v) |> not then
            result <- v :: result
    result        

for i in 0 .. 1000000 do
    let x = posMaskSearch ()
    ()

for i in 0 .. 1000000 do
    let x = itterSearch ()
    ()


//// Big Union Tests

let union unionf (ms: Map<string,_> seq) = 
    seq { for m in ms do yield! m } 
       |> Seq.groupBy (fun (KeyValue(k,_v)) -> k) 
       |> Seq.map (fun (k,es) -> (k,unionf (Seq.map (fun (KeyValue(_k,v)) -> v) es))) 
       |> Map.ofSeq

let su1 = ShardMap<_,_>(bigu1)
let su2 = ShardMap<_,_>(bigu2)
let su3 = ShardMap<_,_>(bigu3)
let su4 = ShardMap<_,_>(bigu4)
let su5 = ShardMap<_,_>(bigu5)
let su6 = ShardMap<_,_>(bigu6)

let bu1 = Map<_,_>(bigu1)
let bu2 = Map<_,_>(bigu2)
let bu3 = Map<_,_>(bigu3)
let bu4 = Map<_,_>(bigu4)
let bu5 = Map<_,_>(bigu5)
let bu6 = Map<_,_>(bigu6)

for i in 0 .. 100 do
    let umap = [u1;u2;u3;u4] |> ShardMap.Union2 (Seq.sum)
    ()

for i in 0 .. 1000 do
    let umap2 = [su1;su2;su3;su4;su5;su6] |> ShardMap.UnionParallel (List.sum)
    ()

for i in 0 .. 1000 do
    let umapp = [su1;su2;su3;su4;su5;su6] |> ShardMap.UnionParaParallel (List.sum)
    ()

for i in 0 .. 1000 do
    let bumap = [bu1;bu2;bu3;bu4;bu5;bu6] |> union (Seq.sum)
    ()

let bumap = [bu1;bu2;bu3;bu4;bu5;bu6] |> union (Seq.sum)
Map.fold (fun acc _ v -> acc + v ) 0 bumap 
let umap2 = [su1;su2;su3;su4;su5;su6] |> ShardMap.UnionParallel (List.sum)
let umapPP = [su1;su2;su3;su4;su5;su6] |> ShardMap.UnionParaParallel (List.sum)
umap2.Count
umap2.BucketSize
umap2.Fold (fun acc _ v -> acc + v ) 0
let hcon = umap2.GetHashConflicts() 
hcon.Length
umap2.PrintLayout()
umap2.FindDuplications()


IO.File.WriteAllLines(@"F:\Code\MapTests\unionPairs.csv",umap2 |> Seq.map (fun kvp -> sprintf "%s,%i" kvp.Key kvp.Value ))

calcBitMaskDepth Environment.ProcessorCount
64 >>> 3
