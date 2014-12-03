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
    | Call(None, MIName "msg", [String text]) -> Some text
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

    

let rec eval (sb:StringBuilder) i e = 
    let spaces = System.String(' ',i)
    let (~~~) (t:string) = sb.AppendLine (sprintf "%s%s" spaces t) |> ignore
    let (~~)  (t:string) = sb.Append (sprintf "%s%s" spaces t)    |> ignore
    match e with
    | Msg text -> ~~~ (sprintf "msg '%s'" text)
    | Not(rest) -> ~~ "not "; List.iter(eval sb i) rest
    | Dead -> ~~ "dead ";
    | Poisoned -> ~~ "poisoned ";
    | WhileLoop(pred,body) -> 
        ~~ "while "
        eval sb i pred 
        ~~~ ""
        eval sb (i+4) body 
    | _ -> ()

let sb = new StringBuilder()



<@ match target Self with _ -> () | _ -> () @>
[<ReflectedDefinition>]
let c() = dead && poisoned

<@ c() @>


[<ReflectedDefinition>]
let q = 
    <@
        let bt = ["0xe75"; "0xe79"]
        ()
    @>


let c = <@ c() @> 
open Microsoft.FSharp.Reflection.FSharpReflectionExtensions

match c with
| Call(x,y,z) ->Expr.TryGetReflectedDefinition(y)


sb.ToString()

Main()