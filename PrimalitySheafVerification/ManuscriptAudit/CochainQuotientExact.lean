import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import PrimalitySheafVerification.ManuscriptAudit.EtaleCechDirectSum

/-! Positive exactness passes to the quotient in a degreewise short exact
sequence of cochain complexes when the adjacent terms are exact. -/

namespace ManuscriptAudit.CochainQuotientExact

open CategoryTheory
open EtaleCechDirectSum

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev Ab := AddCommGrpCat.{0}
private abbrev C := CochainComplex Ab ℕ

variable (S : ShortComplex C)

private abbrev atDegree (n : ℕ) : ShortComplex Ab :=
  S.map (HomologicalComplex.eval Ab (.up ℕ) n)

private theorem commuting {K L : C} (g : K ⟶ L) (i j : ℕ) (x : K.X i) :
    L.d i j (g.f i x) = g.f j (K.d i j x) :=
  ConcreteCategory.congr_hom (g.comm i j) x

private theorem double_d (K : C) (i j k : ℕ) (x : K.X i) :
    K.d j k (K.d i j x) = 0 :=
  ConcreteCategory.congr_hom (K.d_comp_d i j k) x

/-- Exactness at degree n+2 of the first complex and at degree n+1
of the middle complex give exactness at degree n+1 of the quotient. -/
theorem quotient_exactAt_succ (n : ℕ)
    (h : ∀ i, (atDegree S i).ShortExact)
    (hFirst : S.X₁.ExactAt (n + 2)) (hMiddle : S.X₂.ExactAt (n + 1)) :
    S.X₃.ExactAt (n + 1) := by
  apply (cochainExactAt_succ_iff _ n).mpr
  intro z hz
  obtain ⟨y, hy⟩ := (h (n + 1)).ab_surjective_g z
  change S.g.f (n + 1) y = z at hy
  have hx : S.g.f (n + 2) (S.X₂.d (n + 1) (n + 2) y) = 0 := by
    rw [← commuting, hy, hz]
  obtain ⟨u, hu⟩ := ((ShortComplex.ab_exact_iff (atDegree S (n + 2))).mp
    (h (n + 2)).exact) _ hx
  change S.f.f (n + 2) u = S.X₂.d (n + 1) (n + 2) y at hu
  have hud : S.X₁.d (n + 2) (n + 3) u = 0 := by
    apply (h (n + 3)).ab_injective_f
    change S.f.f (n + 3) (S.X₁.d (n + 2) (n + 3) u) = (S.f.f (n + 3)).hom 0
    rw [← commuting, hu, double_d, map_zero]
  obtain ⟨u₀, hu₀⟩ := (cochainExactAt_succ_iff _ (n + 1)).mp hFirst u hud
  let y₀ := y - S.f.f (n + 1) u₀
  have hy₀ : S.X₂.d (n + 1) (n + 2) y₀ = 0 := by
    change (S.X₂.d (n + 1) (n + 2)).hom (y - S.f.f (n + 1) u₀) = 0
    rw [map_sub]
    change S.X₂.d (n + 1) (n + 2) y -
      S.X₂.d (n + 1) (n + 2) (S.f.f (n + 1) u₀) = 0
    rw [commuting, hu₀, hu, sub_self]
  obtain ⟨w, hw⟩ := (cochainExactAt_succ_iff _ n).mp hMiddle y₀ hy₀
  refine ⟨S.g.f n w, ?_⟩
  rw [commuting, hw]
  have hZero : S.g.f (n + 1) (S.f.f (n + 1) u₀) = 0 :=
    ConcreteCategory.congr_hom (atDegree S (n + 1)).zero u₀
  change (S.g.f (n + 1)).hom (y - S.f.f (n + 1) u₀) = z
  rw [map_sub]
  change S.g.f (n + 1) y - S.g.f (n + 1) (S.f.f (n + 1) u₀) = z
  rw [hy, hZero, sub_zero]

end

end ManuscriptAudit.CochainQuotientExact

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CochainQuotientExact.quotient_exactAt_succ
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
