module HashMap
open System.Collections.Generic





type 

type HashMap<'K,'V  when 'K :> IEqualityComparer<'K> >() =
    let lBound = 0
    let hashAry = ResizeArray<KeyValueNode<'K,'V>>(0)

    member x.Add (k:'K,v:'V) =
        let kvp = KeyValueNode(k,v)
        let hash = k.GetHashCode()
        let bucket = hash % (hashAry.Count)
        if hash < lbound && hashAry.Count then 

type HashMapFactory () =

    member static New() =

    member static 
