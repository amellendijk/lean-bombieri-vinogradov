import Mathlib

open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity Set.indicator _ _ _]
def Set.indicator_positivity : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@Set.indicator $β _ $inst $s $f $a) =>
    let i : Q($β) ← mkFreshExprMVarQ q($β) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    match rbody.toNonneg with
    | some pbody =>
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      assumeInstancesCommute
      return .nonnegative q(Set.indicator_apply_nonneg (s := $s) (fun _ => $pr $a))
    | none => throwError "body not nonneg"
  | _ => throwError "not Set.indicator"
