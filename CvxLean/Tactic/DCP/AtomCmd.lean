import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Minimization
import CvxLean.Tactic.DCP.AtomExt
import CvxLean.Tactic.DCP.AtomSyntax
import CvxLean.Tactic.DCP.AtomCmdElab
import CvxLean.Tactic.DCP.AtomCmdMultiLevel

/-!
# Atom library (command)

This file defines all the versions of the `declare_atom` command. First, we allow atoms with or
without background conditions. Affine atoms are treated separately. Note that they do not really
have a graph implementation, they are already in conic form. We add to extra properties to make sure
that they are indeed affine, which are used only as a sanity check. In our framework, cones are also
atoms, which are again trivial, i.e., they are their own implementation. Thus, we also have a
special command for cones.
-/

namespace CvxLean

open Lean Expr Meta Elab Command

/-- Standard `declare_atom` command (without background conditions). -/
@[command_elab atomCommand] unsafe def elabAtomCommand : CommandElab
  | `(declare_atom $id [ $curv ] $args* : $expr :=
      vconditions $vconds*
      implementationVars $impVars*
      implementationObjective $impObj
      implementationConstraints $impConstrs*
      solution $sols*
      solutionEqualsAtom $solEqAtom
      feasibility $feas*
      optimality $opt
      vconditionElimination $vcondElim*) => do
    let atomData ← liftTermElabM do
      let curv ← elabCurvature curv.raw
      let (argDecls, argKinds) ← elabArgKinds args.rawImpl
      let (expr, bodyTy) ← elabExpr expr.raw argDecls
      let (vconds, vcondMap) ← elabVConditions argDecls vconds.rawImpl
      let (impVars, impVarMap) ← elabImpVars argDecls impVars.rawImpl
      let impObj ← elabImpObj argDecls impVars impObj.raw bodyTy
      let impConstrs ← elabImpConstrs argDecls impVars #[] impConstrs.rawImpl
      let sols ← elabSols argDecls impVars impVarMap sols.rawImpl
      let solEqAtom ← elabSolEqAtom argDecls vconds impObj sols expr solEqAtom.raw
      let feas ← elabFeas argDecls vconds #[] impConstrs sols feas.rawImpl
      let opt ← elabOpt curv argDecls expr #[] impVars impObj impConstrs argKinds opt.raw
      let vcondElim ← elabVCondElim curv argDecls #[] vconds vcondMap impVars impConstrs argKinds
        vcondElim.rawImpl

      let atomData := {
        id := id.getId
        curvature := curv
        expr := expr
        argKinds := argKinds
        bconds := #[]
        vconds := vconds
        impVars := impVars
        impObjFun := impObj
        impConstrs := impConstrs.map (·.snd)
        solution := sols
        solEqAtom := solEqAtom
        feasibility := feas
        optimality := opt
        vcondElim := vcondElim
      }
      return atomData

    let atomData ← liftTermElabM <| canonAtomData atomData.curvature atomData
    let atomData ← addAtomDataDecls id.getId atomData

    liftTermElabM do
      trace[CvxLean.debug] "Adding atom data {atomData}."
      addAtom <| AtomData.graph atomData
  | _ => throwUnsupportedSyntax

/-- Standard `declare_atom` command (with background conditions) -/
@[command_elab atomWithBCondsCommand] unsafe def elabAtomWithBCondsCommand : CommandElab
  | `(declare_atom $id [ $curv ] $args* : $expr :=
      bconditions $bconds*
      vconditions $vconds*
      implementationVars $impVars*
      implementationObjective $impObj
      implementationConstraints $impConstrs*
      solution $sols*
      solutionEqualsAtom $solEqAtom
      feasibility $feas*
      optimality $opt
      vconditionElimination $vcondElim*) => do
    let atomData ← liftTermElabM do
      let curv ← elabCurvature curv.raw
      let (argDecls, argKinds) ← elabArgKinds args.rawImpl
      let (expr, bodyTy) ← elabExpr expr.raw argDecls
      let (bconds, _) ← elabBConds argDecls bconds.rawImpl
      let (vconds, vcondMap) ← elabVConditions argDecls vconds.rawImpl
      let (impVars, impVarMap) ← elabImpVars argDecls impVars.rawImpl
      let impObj ← elabImpObj argDecls impVars impObj.raw bodyTy
      let impConstrs ← elabImpConstrs argDecls impVars bconds impConstrs.rawImpl
      let sols ← elabSols argDecls impVars impVarMap sols.rawImpl
      let solEqAtom ← elabSolEqAtom argDecls vconds impObj sols expr solEqAtom.raw
      let feas ← elabFeas argDecls vconds bconds impConstrs sols feas.rawImpl
      let opt ← elabOpt curv argDecls expr bconds impVars impObj impConstrs argKinds opt.raw
      let vcondElim ← elabVCondElim curv argDecls bconds vconds vcondMap impVars impConstrs argKinds
        vcondElim.rawImpl

      let atomData := {
        id := id.getId
        curvature := curv
        expr := expr
        argKinds := argKinds
        bconds := bconds
        vconds := vconds
        impVars := impVars
        impObjFun := impObj
        impConstrs := impConstrs.map (·.snd)
        solution := sols
        solEqAtom := solEqAtom
        feasibility := feas
        optimality := opt
        vcondElim := vcondElim
      }
      return atomData

    let atomData ← liftTermElabM <| canonAtomData atomData.curvature atomData
    let atomData ← addAtomDataDecls id.getId atomData

    liftTermElabM do
      trace[CvxLean.debug] "Adding atom data {atomData}"
      addAtom <| AtomData.graph atomData
  | _ => throwUnsupportedSyntax

/-- Version of `declare_atom` for affine atoms. While the optimality proof is set up as if the atom
were concave, since it is affine, we can flip all the inequalities. We store both proofs.
TODO: Can this be simplified? -/
@[command_elab affineAtomCommand] unsafe def elabAffineAtomCommand : CommandElab
  | `(declare_atom $id [ affine ] $args* : $expr :=
      bconditions $bconds*
      homogenity $hom
      additivity $add
      optimality $opt) => do
    let atomData ← liftTermElabM do
      let (argDecls, argKinds) ← elabArgKinds args.rawImpl
      let (expr, _bodyTy) ← elabExpr expr.raw argDecls
      let vconds := #[]
      let impVars := #[]
      let impObj := expr
      let impConstrs := #[]
      let sols := #[]
      let solEqAtom ← lambdaTelescope expr fun xs body => do
        return ← mkLambdaFVars xs <| ← mkEqRefl body
      let feas := #[]
      let (bconds, _) ← elabBConds argDecls bconds.rawImpl
      let hom ← elabHom argDecls expr argKinds hom.raw
      check hom -- Property is not saved. This is just a sanity check.
      let add ← elabAdd argDecls expr argKinds add.raw
      check add -- Property is not saved. This is just a sanity check.
      let optConcave ← elabOpt Curvature.Concave argDecls expr bconds impVars impObj impConstrs
        argKinds opt.raw
      let optConvex ←
        withExistingLocalDecls argDecls.toList do
          let xs := argDecls.map (mkFVar ·.fvarId)
          let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
          withLocalDeclsDNondep bconds fun as => do
            withCopyOfMonoXs xs argKinds fun _monoXs ys _monoArgKind => do
              let mut optInverted := optConcave
              let mut i' := 0
              for i in [:xs.size] do
                if argKinds[i]! != ArgKind.Constant ∧ argKinds[i]! != ArgKind.Neither then
                  optInverted := mkApp optInverted ys[i']!
                  i' := i' + 1
                else
                  optInverted := mkApp optInverted xs[i]!
              optInverted := mkAppN optInverted as
              for i in [:xs.size] do
                if argKinds[i]! != ArgKind.Constant ∧ argKinds[i]! != ArgKind.Neither then
                  optInverted := mkApp optInverted xs[i]!
              return ← mkLambdaFVars (xs ++ as ++ ys) optInverted
      let opt ← mkAppM ``And.intro #[optConcave, optConvex]
      let vcondElim := #[]

      let atomData := {
        id := id.getId
        curvature := Curvature.Affine
        expr := expr
        argKinds := argKinds
        vconds := vconds
        bconds := bconds
        impVars := impVars
        impObjFun := impObj
        impConstrs := impConstrs.map (·.snd)
        solution := sols
        solEqAtom := solEqAtom
        feasibility := feas
        optimality := opt
        vcondElim := vcondElim
      }
      return atomData

    let atomData ← addAtomDataDecls id.getId atomData

    liftTermElabM do
      trace[CvxLean.debug] "Addding atom {atomData}"
      addAtom <| AtomData.graph atomData
  | _ => throwUnsupportedSyntax

/-- Version of `declare_command` for cones.
TODO: We probably don't even need `optimality` here. Right now, all cone monotonicites are set to
"neither" to ensure that the terms in conic constraints are affine. -/
@[command_elab coneAtomCommand] unsafe def elabConeAtomCommand : CommandElab
  | `(declare_atom $id [ cone ] $args* : $expr :=
        optimality $opt) => do
    let atomData ← liftTermElabM do
      let (argDecls, argKinds) ← elabArgKinds args.rawImpl
      let (expr, _bodyTy) ← elabExpr expr.raw argDecls (ty := some (mkSort levelZero))
      let vconds := #[]
      let impVars := #[]
      let impObj := expr
      let impConstrs := #[]
      let sols := #[]
      let solEqAtom ← lambdaTelescope expr fun xs body =>
        do return ← mkLambdaFVars xs <| ← mkEqRefl body
      let feas := #[]
      let bconds := #[]
      let opt ← elabOpt Curvature.ConvexSet argDecls expr bconds impVars impObj impConstrs argKinds
        opt.raw
      let vcondElim := #[]

      let atomData := {
        id := id.getId
        curvature := Curvature.ConvexSet
        expr := expr
        argKinds := argKinds
        vconds := vconds
        bconds := bconds
        impVars := impVars
        impObjFun := impObj
        impConstrs := impConstrs.map (·.snd)
        solution := sols
        solEqAtom := solEqAtom
        feasibility := feas
        optimality := opt
        vcondElim := vcondElim
      }
      return atomData

    let atomData ← addAtomDataDecls id.getId atomData

    liftTermElabM do
      trace[CvxLean.debug] "Addding atom {atomData}"
      addAtom <| AtomData.graph atomData
  | _ => throwUnsupportedSyntax

end CvxLean
