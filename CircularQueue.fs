module CircularQueue
open System.Collections.Generic

[<Literal>] 
let private linkLength = 16

type internal Link<'T>(tail : Link<'T>) = 
    member val Tail = tail with get,set  
    member val Items = Array.zeroCreate<'T>(linkLength)

type Queue<'T>(items : 'T seq) =
    let empty = Unchecked.defaultof<Link<'T>>
    let head = Link<'T>(empty)
    let mutable tail = head
    let mutable pos = 0

    let add item = 
        if pos < linkLength then
                tail.Items.[pos] <- item
                pos <- pos + 1
            else
                tail <- Link<'T>(tail)
                tail.Items.[0] <- item
                pos <- 1

    do 
        for item in items do
            add item
    
    member x.AppendOne(item) = add item 
    
    member __.toSeq () =

        let link = head
        let cur = 0
        let last = if head = empty then true else false
        let curStop = pos
        let mutable current = Unchecked.defaultof<'T>

        { new IEnumerator<_> with 
                member self.Current = current
            interface System.Collections.IEnumerator with
                    member self.Current = box self.Current
                    member self.MoveNext() =
                        if cur < linkLength then
                            
                        
                        
                    member self.Reset() = stack <- mapList ()
            interface System.IDisposable with 
                    member self.Dispose() = stack <- [] }


    interface IEnumerable<'T> with 
        member x.GetEnumerator() : IEnumerator<'T> = (
            
             :> IEnumerable<_>).GetEnumerator()
    interface IEnumerable with 
        member x.GetEnumerator() : IEnumerator = ((x :> IEnumerable<'T>).GetEnumerator() :> IEnumerator)



    