module

public import ProofWidgets
open Lean Meta ProofWidgets

public meta section

open ProofWidgets.Jsx in
/-- Copied from `Mathlib.Tactic.Widget.mkCommDiag` to load a custom sty -/
def mkCommDiag (sub : String) (embeds : Array (String × Expr)) : MetaM Html := do
  let embeds ← embeds.mapM fun (s, h) =>
      return (s, <InteractiveCode fmt={← Widget.ppExprTagged h} />)
  return (
    <PenroseDiagram
      embeds={embeds}
      dsl={include_str "commutative.dsl"}
      sty={include_str "commutative.sty"}
      sub={sub} />)

/-- This needs to be `const` instead of `fvar` for arcane pretty printer reasons -/
def ec x := Lean.Expr.const x []
def e2 x := Lean.Expr.const x [.param <| .mkSimple "u", .param <| .mkSimple "v"]
def e3 x := Lean.Expr.const x [.param <| .mkSimple "u", .param <| .mkSimple "v", .param <| .mkSimple "w"]

def sumDiag := mkCommDiag "Object S,A,B
Cell l := MakeCell(A,S)
Cell r := MakeCell(B,S)
IsRightDownDiagonal(l)
IsLeftDownDiagonal(r)"
  #[("S", Lean.mkAppN (e2 ``Sum) #[ec `α, ec `β]), ("A", ec `α), ("B", ec `β), ("l", e2 ``Sum.inl), ("r", e2 ``Sum.inr)]

#html sumDiag

def prodDiag := mkCommDiag "Object P,A,B
Cell f := MakeCell(P,A)
Cell s := MakeCell(P,B)
IsLeftDownDiagonal(f)
IsRightDownDiagonal(s)"
  #[("P", Lean.mkApp2 (e2 ``Prod) (ec `α) (ec `β)), ("A", ec `α), ("B", ec `β), ("f", e2 ``Prod.fst), ("s", e2 ``Prod.snd)]

#html prodDiag

def functorDiag := mkCommDiag "Object A,B,FA,FB
Cell f := MakeCell(A,B)
Cell fa := MakeCell(A,FA)
Cell ff := MakeCell(FA,FB)
Cell fb := MakeCell(B,FB)
IsDownVertical(f)
IsRightHorizontal(fa)
IsDownVertical(ff)
IsRightHorizontal(fb)
IsDashed(fa)
IsDashed(fb)"
  #[("A", ec `α), ("B", ec `β), ("FA", .app (ec `F) (ec `α)), ("FB", .app (ec `F) (ec `β)), ("f", ec `f), ("ff", .app (ec `F) (ec `f))]

#html functorDiag

def functorCompDiag := mkCommDiag "Object A,B,C,FA,FB,FC
Cell f := MakeCell(A,B)
Cell g := MakeCell(B,C)
Cell h := MakeCell(A,C)
Cell fa := MakeCell(A,FA)
Cell ff := MakeCell(FA,FB)
Cell fg := MakeCell(FB,FC)
Cell fh := MakeCell(FA,FC)
Cell ffg := MakeCell(FA,FC)
Cell fc := MakeCell(C,FC)
IsDownVertical(f)
IsDownVertical(g)
IsCurvedRight(h)
IsDownVertical(ff)
IsDownVertical(fg)
IsCurvedRight(fh)
IsCurvedLeft(ffg)
IsRightHorizontal(fa)
IsRightHorizontal(fc)
IsDashed(fa)
IsDashed(fc)"
  -- For some reason I need ```Nat` here for arcane pretty printer reasons
  #[("A", ec `α), ("B", ec `β), ("C", ec `γ), ("FA", .app (ec `F) (ec `α)), ("FB", .app (ec `F) (ec `β)), ("FC", .app (ec `F) (ec `γ)), ("f", ec `f), ("g", ec `g), ("h", Lean.mkApp5 (e3 ``Function.comp) (ec ``Nat) (ec ``Nat) (ec ``Nat) (ec `g) (ec `h)), ("ff", .app (ec `F) (ec `f)), ("fg", .app (ec `F) (ec `g)), ("fh", .app (ec `F) (Lean.mkApp5 (e3 ``Function.comp) (ec ``Nat) (ec ``Nat) (ec ``Nat) (ec `g) (ec `h))), ("ffg", (Lean.mkApp5 (e3 ``Function.comp) (ec ``Nat) (ec ``Nat) (ec ``Nat) (.app (ec `F) (ec `g)) (.app (ec `F) (ec `f))))]

#html functorCompDiag

def natTransDiag := mkCommDiag "Object FX,GX,FY,GY
Cell ax := MakeCell(FX,GX)
Cell ff := MakeCell(FX,FY)
Cell ay := MakeCell(FY,GY)
Cell gf := MakeCell(GX,GY)
IsDownVertical(ax)
IsRightHorizontal(ff)
IsDownVertical(ay)
IsRightHorizontal(gf)"
  #[("FX", .app (ec `F) (ec `x)), ("GX", .app (ec `G) (ec `x)), ("FY", .app (ec `F) (ec `Y)), ("GY", .app (ec `G) (ec `Y)), ("ax", .app (ec `α) (ec `x)), ("ff", .app (ec `F) (ec `f)), ("ay", .app (ec `α) (ec `y)), ("gf", .app (ec `G) (ec `f))]

#html natTransDiag
