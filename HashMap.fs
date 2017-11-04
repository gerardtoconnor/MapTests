module HashMap

open MapOld
open SampleData

#if INTERACTIVE
    #time
#endif

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
// open Internal.Utilities
// open Internal.Utilities.Collections


//[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
[<NoEquality; NoComparison>]
type MapTree<'Key,'T> = 
    | MapEmpty 
    | MapOne of 'Key * 'T
    | MapNode of 'Key * 'T * MapTree<'Key,'T> *  MapTree<'Key,'T> * int


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module MapTree = 

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

    
    ///// Additional add single map entry
    let fromOne (k:'Key,v:'T) = MapOne(k,v)


////////////////////////////
////////////////////////
///Shard Map
////////////////////
///////////////////////////

type Shard<'K,'V> = MapTree<'K,'V> []

type MapPos<'K,'V> =
    struct
    val bi : int
    val si : int
    val map : MapTree<'K,'V>
    end
    new(b,s,m) = {bi= b;si=s;map=m}


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

/// Shard Map
////////////////////////////

type ShardMap<'K,'V  when 'K : equality and 'K : comparison >(icount:int, nBucket:Shard<'K,'V> []) =

    let empty = Array.zeroCreate<MapTree<'K,'V>>(ShardSize)

    //let mutable subMapHead = ihead
    let comparer = LanguagePrimitives.FastGenericComparer<'Key>

    let mutable bucket = nBucket
    let countRef = ref icount

    //Lock variables
    ///////////////////////////////////
    let mutable resizing = false // lightweight single op read var for checking state
    let resizeLock = obj()  // lock for when internal bucket array needs to resize


    //let calcBitMaskDepth itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))
    let mutable bitMaskDepth = (calcBitMaskDepth icount)
    
    let mutable bucketBitMask = calcSubBitMask bitMaskDepth

    let mutable capacity = (bucket.Length * ShardSize) - 1
    
    let mutable mapCache = []

    /// Internal Funtions
    /////////////////////////////////////////////////

    let newShard oary = 
        let nary = Array.zeroCreate<MapTree<'K,'V>>(ShardSize)
        Array.Copy(oary,nary,ShardSize)
        nary

    let mapList () =
        match mapCache with
        | [] -> 
            let mutable result = []
            for bi in 0 .. bucket.Length - 1 do
                for si in 0 .. ShardSize - 1 do
                    if not(isEmpty bucket.[bi].[si]) then
                        result <- bucket.[bi].[si] :: result
            mapCache <- result
            result                                 
        | result -> 
            result

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
                                let mutable shrd0 = newBucket.[i0]
                                if isEmpty shrd0 then
                                    shrd0 <- Array.zeroCreate<_>(ShardSize)
                                    newBucket.[i0] <- shrd0
                                
                                if isEmpty shrd0.[j] then
                                    shrd0.[j] <- m0
                                
                            if not (MapTree.isEmpty m1) then
                                let mutable shrd1 = newBucket.[i1]
                                if isEmpty shrd1 then
                                    shrd1 <- Array.zeroCreate<_>(ShardSize)
                                    newBucket.[i1] <- shrd1
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
        let shrd = newShard bucket.[bi]

        lock bucket.SyncRoot (fun () -> bucket.[bi] <- shrd)

        mapCache <- []  // clear the mapCache, next call to seq can rebuild with new map refs

        let m = shrd.[si]
        if isEmpty m then
            shrd.[si] <- MapTree.MapOne (k,v)
            countRef := Interlocked.Increment(countRef)
        else
            if not(MapTree.mem comparer k m) then 
                countRef := Interlocked.Increment(countRef)
            
            shrd.[si] <- MapTree.add comparer k v m

    let remove(k:'K) =
        let kh = k.GetHashCode()
        let bi = bucketIndex(kh,bucketBitMask)
        let si = shardIndex kh
        let shrd = newShard bucket.[bi]
        
        lock bucket.SyncRoot (fun () -> bucket.[bi] <- shrd )

        mapCache <- []  // clear the mapCache, next call to seq can rebuild with new map refs

        let m = shrd.[si]
        if isEmpty m then
            raise <| KeyNotFoundException(sprintf "Key:'%A' not found in map so cannot remove" k)
        else
            Interlocked.Decrement(countRef) |> ignore
            shrd.[si] <- MapTree.remove comparer k m


    let mapFold (f:MapTree<'K,'V> -> 'S -> 'S) (state:'S) =
        let rec go(ls,acc) = 
            match ls with
            | [] -> acc
            | h :: t -> 
                go(t,f h acc)
        go(mapList() , state)

    let transpose (fn:MapTree<'K,'V> -> MapTree<'K,'T>) =
        let nBucket = Array.zeroCreate<Shard<'K,'T>>(bucket.Length)
        Tasks.Parallel.For(0, bucket.Length,
             fun bi ->
        //for bi in 0 .. bucket.Length - 1 do
                for si in 0 .. ShardSize - 1 do
                    let m = bucket.[bi].[si]
                    if not(isEmpty m) then
                        if isEmpty nBucket.[bi] then nBucket.[bi] <- Array.zeroCreate<MapTree<'K,'T>>(ShardSize)
                        nBucket.[bi].[si] <- fn m
        ) |> ignore
        ShardMap<'K,'T>(!countRef,nBucket)

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


    member __.Fold (foldFn:'S -> 'K -> 'V  -> 'S) (istate:'S) = 
        // let mutable state = istate
        // for kvp in x do
        //     state <- foldFn kvp.Key kvp.Value state
        // state       
        mapFold (fun m acc -> MapTree.fold foldFn acc m) istate

    member __.Partition (predicate:'K -> 'V -> bool) = mapFold (fun m acc -> MapTree.partitionAux comparer (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(predicate)) m acc) (MapEmpty,MapEmpty)

    member __.Map (mapFn:'V -> 'T) : ShardMap<'K,'T> = transpose (MapTree.map mapFn)
        // let nBucket = Array.zeroCreate<MapTree<'K,'T> []>(bucket.Length)
        // for bi in 0 .. bucket.Length - 1 do
        //     for si in 0 .. ShardSize - 1 do
        //         if not(isEmpty bucket.[bi].[si]) then
        //             if isEmpty nBucket.[bi] then nBucket.[bi] <- Array.zeroCreate<MapTree<'K,'T>>(ShardSize)
        //             nBucket.[bi].[si] <- MapTree.map mapFn bucket.[bi].[si]
        // ShardMap<'K,'T>(!countRef,nBucket)
    
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
                        | MapEmpty :: rest -> go rest
#if ONE
                        | MapOne (k,v) :: rest -> 
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- rest
                            true
#else
                        | (MapNode(k,v,MapEmpty,MapEmpty,_)) :: rest -> 
                      
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- rest
                            true
#endif                        
                        | (MapNode(k,v,l,r,_)) :: rest ->             
                            current <- new KeyValuePair<_,_>(k,v)
                            stack <- l :: r :: rest
                            true
                        | [] -> false
                    go stack

                  member self.Reset() = stack <- mapList ()
            interface System.IDisposable with 
                  member self.Dispose() = stack <- [] }


////////////////

    member __.Count = !countRef

    member __.BucketSize = bucket.Length

    member __.MapList = mapList()

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
        override s.GetEnumerator() = (s.toSeq () :> System.Collections.IEnumerator)

    static member Union (maps:ShardMap<_,_> seq) =
        let mutable cache = []
        let mutable counter = 0
        let mutable maxBucket = 0 
        for map in maps do
            counter <- counter + 1
            if map.BucketSize > maxBucket then maxBucket <- map.BucketSize 
            cache <- map :: cache


    new(counter:int,items:('K * 'V) seq) =

        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let bitdepth = (calcBitMaskDepth counter)
        let bucketSize = pow2 (bitdepth)
        let bucketBitMask = calcSubBitMask bitdepth
        let newBucket = Array.zeroCreate<Shard<'K,'V>>(bucketSize)

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
                        MapTree.MapOne (k,v)
                    else
                        //printfn "+| adding key:'%A' [%i][%i] for value:%A to map {%A}" k bi si v m
                        MapTree.add comparer k v m                        
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

    new(kvps:('K * 'V) []) =      
        ShardMap<_,_>(kvps.Length,kvps)
        
  
 

///////////////////////////////////////////////
///////////////////////////////////////////////
// The END
///////////////////////////////////////////////
///////////////////////////////////////////////

let bprint (value:int) = Convert.ToString(value, 2).PadLeft(32, '0')

let smap = new ShardMap<_,_>(numberStrings)

let nmap = smap.Map int
nmap.["98549420"]
//    ("98549420","1618963");

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
let bmap = Map<_,_>(numberStrings)

for i in 0 .. 1000 do
    let nsmap = smap.Map int
    ()

for i in 0 .. 1000 do
    let nbmap = Map.map (fun _ v -> int v) bmap
    ()
////////////////////////////////////////
for i in 0 .. 10000 do
    let nsmap = smap.Fold (fun acc _ _ -> acc + 1) 0
    ()

for i in 0 .. 10000 do
    let nbmap = Map.fold (fun acc _ _ -> acc + 1 ) 0 bmap
    ()
#time

smap.BucketSize
smap.Count
smap |> Seq.length
smap.PrintLayout()
let sml = smap.SubMapList()
calcBitMaskDepth smap.Count
List.length sml

2 <<< (11-5)

let dict = Dictionary<string,string>()
for (k,v) in numberStrings do
    dict.Add(k,v)

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
let ittrLoops = 10000

let mutable counter = 0
printfn "coutner:%i" counter

for i in 0 .. ittrLoops do
    smap |> Seq.iter (fun kvp -> 
        let k = kvp.Key
        let v = kvp.Value
        // counter <- counter + 1
        ()
    )

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