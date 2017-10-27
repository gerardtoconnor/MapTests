module MapOld

//#nowarn "51"
//#nowarn "69" // interface implementations in augmentations
//#nowarn "60" // override implementations in augmentations

open Microsoft.FSharp.Core
open Microsoft.FSharp.Core.Operators
open Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators
open System
open System.Collections.Generic
// open Internal.Utilities
// open Internal.Utilities.Collections


    //[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
    [<NoEquality; NoComparison>]
    type MapTree<'Key,'T> = 
        | MapEmpty 
#if ONE 
        | MapOne of 'Key * 'T
#endif
        | MapNode of 'Key * 'T * MapTree<'Key,'T> *  MapTree<'Key,'T> * int


    [<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
    module MapTree = 

        let empty = MapEmpty 

        let inline height x  = 
          match x with 
          | MapEmpty -> 0
#if ONE 
          | MapOne _ -> 1
#endif
          | MapNode(_,_,_,_,h) -> h

        let inline isEmpty m = 
            match m with 
            | MapEmpty -> true
            | _ -> false

        let inline mk l k v r = 
#if ONE 
            match l,r with 
            | MapEmpty,MapEmpty -> MapOne(k,v)
            | _ -> 
#endif
                let hl = height l 
                let hr = height r 
                let m = if hl < hr then hr else hl 
                MapNode(k,v,l,r,m+1)

        let rebalance t1 k v t2 =
            let t1h = height t1
            let t2h = height t2
            if t2h > t1h + 2 then // right is heavier than left 
                match t2 with 
                | MapNode(t2k,t2v,t2l,t2r,_) -> 
                   // one of the nodes must have height > height t1 + 1 
                   if height t2l > t1h + 1 then  // balance left: combination 
                     match t2l with 
                     | MapNode(t2lk,t2lv,t2ll,t2lr,_) ->
                        mk (mk t1 k v t2ll) t2lk t2lv (mk t2lr t2k t2v t2r) 
                     | _ -> failwith "rebalance"
                   else // rotate left 
                     mk (mk t1 k v t2l) t2k t2v t2r
                | _ -> failwith "rebalance"
            else
                if t1h > t2h + 2 then // left is heavier than right 
                  match t1 with 
                  | MapNode(t1k,t1v,t1l,t1r,_) -> 
                    // one of the nodes must have height > height t2 + 1 
                      if height t1r > t2h + 1 then 
                      // balance right: combination 
                        match t1r with 
                        | MapNode(t1rk,t1rv,t1rl,t1rr,_) ->
                            mk (mk t1l t1k t1v t1rl) t1rk t1rv (mk t1rr k v t2)
                        | _ -> failwith "rebalance"
                      else
                        mk t1l t1k t1v (mk t1r k v t2)
                  | _ -> failwith "rebalance"
                else mk t1 k v t2

        let rec sizeAux acc m = 
            match m with  
            | MapEmpty -> acc
#if ONE 
            | MapOne _ -> acc + 1
#endif
            | MapNode(_,_,l,r,_) -> sizeAux (sizeAux (acc+1) l) r 

#if ONE 
#else
        let MapOne(k,v) = MapNode(k,v,MapEmpty,MapEmpty,1)
#endif
        
        let count x = sizeAux 0 x

        let rec add (comparer: IComparer<'T>) k v m = 
            match m with 
            | MapEmpty -> MapOne(k,v)
#if ONE 
            | MapOne(k2,v2) -> 
                let c = comparer.Compare(k,k2) 
                if c < 0   then MapNode (k,v,MapEmpty,m,2)
                elif c = 0 then MapOne(k,v)
                else            MapNode (k,v,m,MapEmpty,2)
#endif
            | MapNode(k2,v2,l,r,h) -> 
                let c = comparer.Compare(k,k2) 
                if c < 0 then rebalance (add comparer k v l) k2 v2 r
                elif c = 0 then MapNode(k,v,l,r,h)
                else rebalance l k2 v2 (add comparer k v r) 

        let indexNotFound() = raise (new System.Collections.Generic.KeyNotFoundException("An index satisfying the predicate was not found in the collection"))

        let rec find (comparer: IComparer<'T>) k m = 
            match m with 
            | MapEmpty -> indexNotFound()
#if ONE 
            | MapOne(k2,v2) -> 
                let c = comparer.Compare(k,k2) 
                if c = 0 then v2
                else indexNotFound()
#endif
            | MapNode(k2,v2,l,r,_) -> 
                let c = comparer.Compare(k,k2) 
                if c < 0 then find comparer k l
                elif c = 0 then v2
                else find comparer k r

        let rec tryFind (comparer: IComparer<'T>) k m = 
            match m with 
            | MapEmpty -> None
#if ONE 
            | MapOne(k2,v2) -> 
                let c = comparer.Compare(k,k2) 
                if c = 0 then Some v2
                else None
#endif
            | MapNode(k2,v2,l,r,_) -> 
                let c = comparer.Compare(k,k2) 
                if c < 0 then tryFind comparer k l
                elif c = 0 then Some v2
                else tryFind comparer k r

        let partition1 (comparer: IComparer<'T>) f k v (acc1,acc2) = 
            if f k v then (add comparer k v acc1,acc2) else (acc1,add comparer k v acc2) 
        
        let rec partitionAux (comparer: IComparer<'T>) f s acc = 
            match s with 
            | MapEmpty -> acc
#if ONE 
            | MapOne(k,v) -> partition1 comparer f k v acc
#endif
            | MapNode(k,v,l,r,_) -> 
                let acc = partitionAux comparer f r acc 
                let acc = partition1 comparer f k v acc
                partitionAux comparer f l acc

        let partition (comparer: IComparer<'T>) f s = partitionAux comparer f s (empty,empty)

        let filter1 (comparer: IComparer<'T>) f k v acc = if f k v then add comparer k v acc else acc 

        let rec filterAux (comparer: IComparer<'T>) f s acc = 
            match s with 
            | MapEmpty -> acc
#if ONE 
            | MapOne(k,v) -> filter1 comparer f k v acc
#endif
            | MapNode(k,v,l,r,_) ->
                let acc = filterAux comparer f l acc
                let acc = filter1 comparer f k v acc
                filterAux comparer f r acc

        let filter (comparer: IComparer<'T>) f s = filterAux comparer f s empty

        let rec spliceOutSuccessor m = 
            match m with 
            | MapEmpty -> failwith "internal error: Map.splice_out_succ_or_pred"
#if ONE 
            | MapOne(k2,v2) -> k2,v2,MapEmpty
#endif
            | MapNode(k2,v2,l,r,_) ->
                match l with 
                | MapEmpty -> k2,v2,r
                | _ -> let k3,v3,l' = spliceOutSuccessor l in k3,v3,mk l' k2 v2 r

        let rec remove (comparer: IComparer<'T>) k m = 
            match m with 
            | MapEmpty -> empty
#if ONE 
            | MapOne(k2,v2) -> 
                let c = comparer.Compare(k,k2) 
                if c = 0 then MapEmpty else m
#endif
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

        let rec containsKey (comparer: IComparer<'T>) k m = 
            match m with 
            | MapEmpty -> false
#if ONE 
            | MapOne(k2,v2) -> (comparer.Compare(k,k2) = 0)
#endif
            | MapNode(k2,_,l,r,_) -> 
                let c = comparer.Compare(k,k2) 
                if c < 0 then containsKey comparer k l
                else (c = 0 || containsKey comparer k r)

        let rec iter f m = 
            match m with 
            | MapEmpty -> ()
#if ONE 
            | MapOne(k2,v2) -> f k2 v2
#endif
            | MapNode(k2,v2,l,r,_) -> iter f l; f k2 v2; iter f r

        let rec first f m = 
            match m with 
            | MapEmpty -> None
#if ONE 
            | MapOne(k2,v2) -> f k2 v2 
#endif
            | MapNode(k2,v2,l,r,_) -> 
                match first f l with 
                | Some _ as res -> res 
                | None -> 
                match f k2 v2 with 
                | Some _ as res -> res 
                | None -> first f r

        let rec exists f m = 
            match m with 
            | MapEmpty -> false
#if ONE 
            | MapOne(k2,v2) -> f k2 v2
#endif
            | MapNode(k2,v2,l,r,_) -> f k2 v2 || exists f l || exists f r

        let rec forAll f m = 
            match m with 
            | MapEmpty -> true
#if ONE 
            | MapOne(k2,v2) -> f k2 v2
#endif
            | MapNode(k2,v2,l,r,_) -> f k2 v2 && forAll f l && forAll f r

        let rec map f m = 
            match m with 
            | MapEmpty -> empty
#if ONE 
            | MapOne(k,v) -> MapOne(k,f v)
#endif
            | MapNode(k,v,l,r,h) -> let v2 = f v in MapNode(k,v2,map f l, map f r,h)

        let rec mapi f m = 
            match m with
            | MapEmpty -> empty
#if ONE 
            | MapOne(k,v) -> MapOne(k,f k v)
#endif
            | MapNode(k,v,l,r,h) -> let v2 = f k v in MapNode(k,v2, mapi f l, mapi f r,h)

        // Fold, right-to-left. 
        //
        // NOTE: This differs from the behaviour of Set.fold which folds left-to-right.
        let rec fold f m x = 
            match m with 
            | MapEmpty -> x
#if ONE 
            | MapOne(k,v) -> f k v x
#endif
            | MapNode(k,v,l,r,_) -> fold f l (f k v (fold f r x))

        let foldSection (comparer: IComparer<'T>) lo hi f m x =
            let rec fold_from_to f m x = 
                match m with 
                | MapEmpty -> x
#if ONE 
                | MapOne(k,v) ->
                    let clo_k = comparer.Compare(lo,k)
                    let ck_hi = comparer.Compare(k,hi)
                    let x = if clo_k <= 0 && ck_hi <= 0 then f k v x else x
                    x
#endif
                | MapNode(k,v,l,r,_) ->
                    let clo_k = comparer.Compare(lo,k)
                    let ck_hi = comparer.Compare(k,hi)
                    let x = if clo_k < 0                then fold_from_to f l x else x
                    let x = if clo_k <= 0 && ck_hi <= 0 then f k v x                     else x
                    let x = if ck_hi < 0                then fold_from_to f r x else x
                    x
           
            if comparer.Compare(lo,hi) = 1 then x else fold_from_to f m x

        let rec foldMap (comparer: IComparer<'T>) f m z acc = 
            match m with 
            | MapEmpty -> acc,z
#if ONE 
            | MapOne(k,v) -> 
                let v',z = f k v z
                add comparer k v' acc,z
#endif
            | MapNode(k,v,l,r,_) -> 
                let acc,z = foldMap comparer f r z acc
                let v',z = f k v z
                let acc = add comparer k v' acc 
                foldMap comparer f l z acc

        let toList m = fold (fun k v acc -> (k,v) :: acc) m []
        let toArray m = m |> toList |> Array.ofList
        let ofList comparer l = List.fold (fun acc (k,v) -> add comparer k v acc) empty l

        
        let rec mkFromEnumerator comparer acc (e : IEnumerator<_>) = 
            if e.MoveNext() then 
                let (x,y) = e.Current 
                mkFromEnumerator comparer (add comparer x y acc) e
            else acc
          
        let ofSeq comparer (c : seq<_>) =
            use ie = c.GetEnumerator()
            mkFromEnumerator comparer empty ie 
          
        let copyToArray s (arr: _[]) i =
            let j = ref i 
            s |> iter (fun x y -> arr.[!j] <- KeyValuePair(x,y); j := !j + 1)


        /// Imperative left-to-right iterators.
        type MapIterator<'Key,'T>(s:MapTree<'Key,'T>) = 
            // collapseLHS:
            // a) Always returns either [] or a list starting with SetOne.
            // b) The "fringe" of the set stack is unchanged. 
            let rec collapseLHS stack =
                match stack with
                | []                           -> []
                | MapEmpty             :: rest -> collapseLHS rest
#if ONE 
                | MapOne _         :: _ -> stack
#else
                | (MapNode(_,_,MapEmpty,MapEmpty,_)) :: _ -> stack
#endif
                | (MapNode(k,v,l,r,_)) :: rest -> collapseLHS (l :: MapOne (k,v) :: r :: rest)
          
              /// invariant: always collapseLHS result 
            let mutable stack = collapseLHS [s]
               /// true when MoveNext has been called   
            let mutable started = false

            let notStarted() = raise (new System.InvalidOperationException("Enumeration has not started. Call MoveNext."))
            let alreadyFinished() = raise (new System.InvalidOperationException("Enumeration already finished."))

            member i.Current =
                if started then
                    match stack with
#if ONE
                      | MapOne (k,v) :: _ -> new KeyValuePair<_,_>(k,v)
#else
                      | (MapNode(k,v,MapEmpty,MapEmpty,_)) :: _ -> new KeyValuePair<_,_>(k,v)
#endif
                      | []            -> alreadyFinished()
                      | _             -> failwith "Please report error: Map iterator, unexpected stack for current"
                else
                    notStarted()

            member i.MoveNext() =
              if started then
                match stack with
#if ONE
                  | MapOne _ :: rest -> 
#else
                  | (MapNode(_,_,MapEmpty,MapEmpty,_)) :: rest -> 
#endif
                      stack <- collapseLHS rest;
                      not stack.IsEmpty
                  | [] -> false
                  | _ -> failwith "Please report error: Map iterator, unexpected stack for moveNext"
              else
                  // The first call to MoveNext "starts" the enumeration. 
                  started <- true;  
                  not stack.IsEmpty

        let toSeq s = 
            let i = ref (MapIterator(s))
            { new IEnumerator<_> with 
                  member self.Current = (!i).Current
              interface System.Collections.IEnumerator with
                  member self.Current = box (!i).Current
                  member self.MoveNext() = (!i).MoveNext()
                  member self.Reset() = i :=  MapIterator(s)
              interface System.IDisposable with 
                  member self.Dispose() = ()}
