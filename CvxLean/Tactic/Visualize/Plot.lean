import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts

import CvxLean.Lib.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Tactic.Solver.Float.RealToFloat

namespace CvxLean

open Lean 

namespace Command

open Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command

open Lean.PrettyPrinter.Delaborator

open ProofWidgets Recharts Json Server

-- Copied from ProofWidgets/Demo/Plot

open scoped ProofWidgets.Jsx in
open scoped ProofWidgets.Json in
def Plot (fn : Float → Float) (a b : Float) (steps := 100) : THtml :=
  let jsonData : Array Json :=
    Nat.fold (flip Array.push) (steps + 1) #[]
    |> Array.map (fun (t : Nat) => 
        let t : Float := t.toFloat / steps.toFloat;  
        let x := a + t * (b - a);
        (x, fn x))
    |> Array.map (fun (x,y) => json% {x: $(toJson x) , y: $(toJson y)});
  <LineChart width={400} height={400} data={jsonData}>
    <XAxis domain?={#[toJson a, toJson b]} dataKey?="x" />
    <YAxis domain?={#[toJson (-1), toJson 1]} allowDataOverflow={Bool.false} />
    <Line type={.monotone} dataKey="y" stroke="#8884d8" dot?={Bool.false} />
  </LineChart>

syntax (name := plot1D) "#plot1D " term " [[" term ", " term "]]" : command

/-- -/
@[command_elab «plot1D»]
unsafe def evalPlot1D : CommandElab := fun stx => match stx with
| `(#plot1D $probInstance:term [[$a:term, $b:term]]) => do
  let f ← liftTermElabM <| do 
      let probTerm ← elabTerm probInstance.raw none
      let probTerm ← whnf probTerm
      let probTerm ← instantiateMVars probTerm

      -- TODO(RFM): Move into a function. This is the issue from solve.
      for mvarId in ← getMVars probTerm do 
        try {
          let mvarVal ← synthInstance (← mvarId.getDecl).type
          mvarId.assign mvarVal }
        catch _ => pure ()

      liftMetaM <| do 
        match probTerm with 
        | (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const `Minimization.mk _)
              domain') codomain') objFun) constraints) => do 
            let objFunF ← realToFloat objFun


            let objFunFTerm ← Lean.PrettyPrinter.delab objFunF

            return objFunFTerm
        | _ => throwError "Cannot read problem"
    
    dbg_trace "f : {f}"
    dbg_trace "a : {a}"
    dbg_trace "b : {b}"

    runTermElabM fun _ => do
    let ht ← evalHtml <| ← `(ProofWidgets.Html.ofTHtml (Plot $f $a $b))
    savePanelWidgetInfo stx ``HtmlDisplayPanel do
      return json% { html: $(← rpcEncode ht) }
| _ => throwUnsupportedSyntax

end Command

end CvxLean
