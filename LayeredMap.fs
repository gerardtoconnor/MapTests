module LayeredMap

open System.Collections.Generic
open System.Collections.Generic
open System

type LayeredMap<'K,'V when 'K : equality>(parent:LayeredMap<'K,'V>) =
    let table = Dictionary<'K,'V>()           

    member private __.table = table
    member private __.parent = parent

    member inline __.Add (k,v) = table.Add(k,v)
    member inline __.Remove k = table.Remove k
    
    member __.Item (k:'K) : 'V =
        let mutable result = Unchecked.defaultof<'V>
        match table.TryGetValue(k,&result) with
        | true -> result
        | false -> raise (KeyNotFoundException())

    member __.TryGetValue (key:'K,result : byref<'V>) =
        //let mutable result = Unchecked.defaultof<'V>
        match table.TryGetValue(key,&result) with
        | true -> true
        | false ->
            if Object.ReferenceEquals(null,parent) then
                false
            else
                match parent.TryGetValue(key,&result) with
                | true -> true
                | false -> false
         

    member x.Child () = LayeredMap<'K,'V>(x)

    member __.toSeq () =

        let mutable cur = table.GetEnumerator()
        let mutable next = parent

        let rec go () =
            if cur.MoveNext() then true
            else
                if Object.ReferenceEquals(null,next) then false
                else
                    cur <- next.table.GetEnumerator()                                                       
                    next <- next.parent
                    go ()

        { new IEnumerator<_> with 
                member self.Current = cur.Current
            interface System.Collections.IEnumerator with
                    member self.Current = box self.Current
                    member self.MoveNext() = go ()                               

                    member self.Reset() = 
                        cur <- table.GetEnumerator()
                        next <- parent
            interface System.IDisposable with 
                    member self.Dispose() = ()
                    }
    static member New() = LayeredMap<'K,'V>(Unchecked.defaultof<LayeredMap<'K,'V>>)

