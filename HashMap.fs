module HashMap
open System.Collections.Generic
open System


type Buffer<'K,'V when 'K :comparison>() =

    let [<Literal>] ShardSize = 8
    let buffer = ResizeArray<Map<'K,'V> []>(32)

    let locks = ResizeArray<obj>(32)

    let rental = ResizeArray<int>(32)

    let mutable freeList : int list = []
    //let mutable freeListCount = 0

    member __.Rent() =
        match freeList with
        | [] ->
            let newBuffer = Array.zeroCreate<Map<'K,'V>>(ShardSize) 
            let index = buffer.Count
            buffer.Add newBuffer
            rental.Add 1
            (index,newBuffer)
        | h :: t -> 
            freeList <- t
            rental.[h] <- 1
            (h,buffer.[h])

    member __.Return(index:int , ary: Map<'K,'V> [] ) =
        match rental.[index] with
        | 0 -> failwith "A buffer as been returned when with rentals already zero"
        | 1 ->    
            System.Array.Clear(ary,0,ShardSize)
            rental.[index] <- 0
            freeList <- index :: freeList
        | x ->
            rental.[index] <- x - 1

type BufferFactory() =
    let buffers = Dictionary<System.Type,obj>()
    member __.GetBuffer<'K,'V when 'K : comparison>() =
        let t = typeof<'K * 'V>
        match buffers.TryGetValue t with
        | true, v -> v :?> Buffer<'K,'V> 
        | false,_ ->
            let newBuf = Buffer<'K,'V>()
            buffers.Add(t, newBuf)
            newBuf

type ShardMap<'K,'V  when 'K :> IEqualityComparer<'K> and 'K : comparison>(bf: BufferFactory) =
    
    let buffer =  bf.GetBuffer<'K,'V>()
    let hashAry = ResizeArray<Map<'K,'V> []>(0)
    
    let mutable count = 0 

    let bucketSize itemCount = int(Math.Ceiling(Math.Log(float itemCount) / Math.Log(float 2)))
    let last 
    let bitMask (keyHash:int) (arySize) = ( (keyHash <<< (32 - arySize)) <<< (35 - arySize) , keyHash &&& 0b111 )


        if count + 1 < (hashAry.Count * 8) then 
            // base array needs resizing

        else 


        let kvp = KeyValueNode(k,v)
        let hash = k.GetHashCode()
        let bucket = hash % (hashAry.Count)
        if hash < lbound && hashAry.Count then
        ()
