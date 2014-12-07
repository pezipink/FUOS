// F# -> UOSTEAM compiler

// THINGS TO NOTE!  

// Whilst you are able to achieve recursion in UOSteam by calling yourself, there is no way to RETURN to the place you came from
// when you make a jump it is final!  This means you cannot do non-tail call recursion withouht some extra state

// Basics :

// UOS has global object state

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open System.Reflection
open System.Text
open Microsoft.FSharp.Reflection


let (|MIName|_|) name (mi:MethodInfo) =
    if mi.Name = name then Some() else None

let (|PIName|_|) name (pi:PropertyInfo) =
    if pi.Name = name then Some() else None

let (|UCName|_|) name (ui:UnionCaseInfo) =
    if ui.Name = name then Some() else None

type Spell =
    | Cure
    | Heal

type TargetTypes =
    | Self    


// these are dummy functions / props used to generate the UOS equivalent functions
[<ReflectedDefinition>]
let msg (text:string) = ()

[<ReflectedDefinition>]
let waitForTarget (ms:int) = ()

[<ReflectedDefinition>]
let target (t:TargetTypes) = ()

[<ReflectedDefinition>]
let pause (ms:int) = ()

[<ReflectedDefinition>]
let dead = false

[<ReflectedDefinition>]
let poisoned = false

let (|Msg|_|) = function
    | Call(None, MIName "msg", [v]) -> Some v
    | _ -> None
    
let (|ListIter|_|) = function
     |Call (None, MIName "Iterate", (Lambda(v,f) )::(Var listName)::rest) -> 
        Some(v.Name,f,listName.Name,rest)
     | _ -> None

let (|WaitForTarget|_|) = function
    | Call(None, MIName "waitForTarget", [Int32 ms]) -> Some ms
    | _ -> None

let (|Target|_|) = function
    | Call(None, MIName "target", [NewUnionCase(ui,_) ]) -> 
        match ui.Name with
        | "Self" -> Some Self
        | _  -> None       
    | _ -> None

let (|Not|_|) = function
    | Call(None, MIName "Not", rest) -> Some rest
    | _ -> None

let (|Dead|_|) = function
    | PropertyGet(None, PIName "dead", _ ) -> Some() 
    | _ -> None

let (|Poisoned|_|) = function
    | PropertyGet(None, PIName "poisoned", _ ) -> Some() 
    | _ -> None

let (|IntList|_|) = function
    | NewUnionCase(ui,Value(_)::_) as this when ui.DeclaringType = typeof<List<int>> ->  
        let rec aux r = function
            | NewUnionCase(ui,Value(v,_)::rest) -> 
                match rest with 
                | [next] -> aux((v :?> int)::r) next
                | _ -> r
            | _ -> r
        Some(aux [] this)
    | _ -> None


let (|StringList|_|) = function
    | NewUnionCase(ui,Value(_)::_) as this when ui.DeclaringType = typeof<List<string>> ->  
        let rec aux r = function
            | NewUnionCase(ui,Value(v,_)::rest) -> 
                match rest with 
                | [next] -> aux((v :?> string)::r) next
                | _ -> r
            | _ -> r
        Some(aux [] this)
    | _ -> None

type env =
    { lists : Map<string, list<string>> 
      identifiers : Map<string, string> 
      tab : int
      sb : StringBuilder }

let rec eval env e = 
    let spaces = System.String(' ',env.tab)
    let (~~~) (t:string) = env.sb.AppendLine (sprintf "%s%s" spaces t) |> ignore
    let (~~)  (t:string) = env.sb.Append (sprintf "%s%s" spaces t)     |> ignore
    match e with
    | Msg(String text) -> ~~~ (sprintf "msg '%s'" text)    
    | Msg(Var text) -> ~~~ (sprintf "msg '%s'" env.identifiers.[text.Name])
    | Not(rest) -> ~~ "not "; List.iter(eval env) rest    
    | Dead -> ~~ "dead ";
    | Poisoned -> ~~ "poisoned ";
    | Let(name, IntList ints , rest) -> 
        ~~~ (sprintf "@createlist %s" name.Name)
        for i in List.rev ints do
            ~~~(sprintf "@pushlist '%s' '%i'" name.Name i)
        eval env rest
    | Let(name, StringList strings , rest) -> 
        ~~~ (sprintf "@createlist %s" name.Name)
        for i in List.rev strings do
            ~~~(sprintf "@pushlist '%s' '%s'" name.Name i)
        eval env rest
    | ListIter(v,f,listName,rest) ->
        ~~~(sprintf "for 0 in '%s'" listName)
        eval {env with tab = env.tab + 1; identifiers = env.identifiers.Add(v,sprintf "%s[]" listName) } f
        ~~~("endfor")
        List.iter(eval env) rest
    | WhileLoop(pred,body) -> 
        ~~ "while "
        eval env pred 
        ~~~ ""
        eval {env with tab = env.tab+4 } body 
    | Sequential(ex, ex2) -> 
        eval env ex
        eval env ex2
    | AndAlso(x,y) -> 
        eval env x
        ~~ " and "
        eval env y
    | OrElse(x,y) -> 
        eval env x
        ~~ " or "
        eval env y
    | IfThenElse(i, t, e) ->
        ~~ "if "
        eval { env with tab = 0} i
        ~~~ ""
        eval { env with tab = env.tab + 1} t
        ~~~ "else "
        eval { env with tab = env.tab + 1} e
        ~~~ "endif "
    // pipe right with inferred lambda
    | Call(None, (|>), leftSide::(Let(_, f,Lambda(v,Call(o,mi,args)) ))::rest ) ->
        match o with
        | Some o -> eval env (Expr.Call(o,mi,[f;leftSide]))
        | None -> eval env (Expr.Call(mi,[f;leftSide]))
    // pipe right with function call
    | Call(None, (|>), leftSide::(Lambda(_,Call(None,mi,[Lambda(_,Call(_,user,args) );_ ])))::rest ) ->
        match Expr.TryGetReflectedDefinition user with
        | Some f -> eval env (Expr.Call(mi,[f;leftSide]))
        | None -> failwith "you must decorate functions with the ReflectedDefinition attribute in order to call them within the program"
        
    | Call(_,mi, args ) as e -> 
        match Expr.TryGetReflectedDefinition mi with
        | Some f -> eval env f
        | None -> failwith "you must decorate functions with the ReflectedDefinition attribute in order to call them within the program"
    | Lambda(arg,f) ->
        eval env f
    | _ -> ()
  
let sb = new StringBuilder()



[<ReflectedDefinition>]
let deadOrPoisoned() = dead && poisoned

[<ReflectedDefinition>]
let test d =
    msg d 
    match deadOrPoisoned() with
    | true -> msg "poisoned"
    | false -> msg "not poisoned"


let getBags tosearch = []
[<ReflectedDefinition>]
let rec bags toSearch =
     seq { yield toSearch 
           for b in getBags toSearch do
            yield! bags b } 



[<ReflectedDefinition>]
let q = 
    <@
        let data = ["a";"b";"c";"d";"e"]
        data |> List.iter test

    @> 
//    <@
//
//
//        let data = ["a";"b";"c";"d";"e"]
//        data |> List.iter test
//        
//
//
//    @> 


let env = { sb = StringBuilder(); tab = 0; lists = Map.empty; identifiers = Map.empty}
//

eval env q

let x = env.sb.ToString()
printfn "%s" x
()
//    
//match q with 
//| Let(name, rest, restt) -> 
//    match rest with 
//    | IntList ints -> ints
//    | _ -> []
//| _ -> []
//
//
////let c = <@ c() @> 
////open Microsoft.FSharp.Reflection.FSharpReflectionExtensions
////
////match c with
////| Call(x,y,z) ->Expr.TryGetReflectedDefinition(y)
//
//
//sb.ToString()
//
