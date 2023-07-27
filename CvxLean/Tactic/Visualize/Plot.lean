import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts

import CvxLean.Lib.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Tactic.Solver.Float.RealToFloat
import CvxLean.Tactic.Visualize.PlotLy

namespace CvxLean

open Lean 

namespace Command

open Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command

open Lean.PrettyPrinter.Delaborator

open ProofWidgets Recharts Json Server

-- Plot 2D.

-- Copied from ProofWidgets/Demo/Plot

open scoped ProofWidgets.Jsx in
open scoped ProofWidgets.Json in
def Plot2D (fn : Float → Float) (a b : Float) (steps := 100) : THtml :=
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

syntax (name := plot1Var) "#plot_1_var " term " [[" term ", " term "]]" : command

-- TODO(RFM): Move.
def getObjFunTerm (probInstance : Term) : TermElabM Term := do
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

/-- -/
@[command_elab «plot1Var»]
def evalPlot1Var : CommandElab := fun stx => match stx with
| `(#plot_1_var $probInstance:term [[$a:term, $b:term]]) => do
    let f ← liftTermElabM <| getObjFunTerm probInstance
    
    runTermElabM fun _ => do
    let ht ← evalHtml <| ← `(ProofWidgets.Html.ofTHtml (Plot2D $f $a $b))
    savePanelWidgetInfo stx ``HtmlDisplayPanel do
      return json% { html: $(← rpcEncode ht) }
| _ => throwUnsupportedSyntax

-- Plot3D

open scoped ProofWidgets.Jsx in
open scoped ProofWidgets.Json in
def Plot3D (fn : Float × Float → Float) (a b c d : Float) (steps := 100) : THtml :=
  let x : Array Float := 
    (Array.range steps).map (fun (t : Nat) => 
        let t : Float := t.toFloat / steps.toFloat;  
        a + t * (b - a));
  let y : Array Float :=
    (Array.range steps).map (fun (t : Nat) => 
        let t : Float := t.toFloat / steps.toFloat;  
        c + t * (d - c));
  let z : Array (Array Float) := x.map (fun x => y.map (fun y => fn (x, y)));
  <PlotLyDisplay 
    x={x}
    y={y}
    z={z} />

syntax (name := plot2Vars) "#plot_2_vars " term " [[" term ", " term "], [" term ", " term "]]" : command

@[command_elab «plot2Vars»]
def evalPlot2Vars : CommandElab := fun stx => match stx with
| `(#plot_2_vars $probInstance:term [[$a:term, $b:term], [$c:term, $d:term]]) => do
    let f ← liftTermElabM <| getObjFunTerm probInstance
    
    runTermElabM fun _ => do
    let ht ← evalHtml <| ← `(ProofWidgets.Html.ofTHtml (Plot3D $f $a $b $c $d))
    savePanelWidgetInfo stx ``HtmlDisplayPanel do
      return json% { html: $(← rpcEncode ht) }
| _ => throwUnsupportedSyntax

end Command

end CvxLean
