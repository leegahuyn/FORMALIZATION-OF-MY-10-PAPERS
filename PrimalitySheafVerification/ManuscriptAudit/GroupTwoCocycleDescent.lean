import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Invariants
import PrimalitySheafVerification.ManuscriptAudit.GroupTwoCocycleConjugation

/-!
# Descent of a degree-two cocycle to fixed coefficients

A cocycle whose mixed terms vanish is constant on cosets in both
arguments and takes values fixed by the subgroup. Its quotient
cocycle uses the native representation on those fixed coefficients.
-/

namespace ManuscriptAudit.GroupTwoCocycleConjugation

open groupCohomology

variable {G A : Type} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (S : Subgroup G) [hS : S.Normal]

/-- A degree-two cocycle with vanishing mixed terms is inflation of an
actual quotient cocycle with values in the subgroup invariants. -/
theorem exists_quotient_cocycle₂ (c : G × G → A) (hc : IsCocycle₂ c)
    (hLeft : ∀ (s : S) (g : G), c (s, g) = 0)
    (hRight : ∀ (g : G) (s : S), c (g, s) = 0) :
    ∃ z : cocycles₂ ((Rep.ofDistribMulAction ℤ G A).quotientToInvariants S),
      ∀ g h : G, (z (QuotientGroup.mk' S g, QuotientGroup.mk' S h)).1 = c (g, h) := by
  let B := (Rep.ofDistribMulAction ℤ G A).quotientToInvariants S
  have h₂ (g h : G) (s : S) : c (g, h * (s : G)) = c (g, h) := by
    have he := hc g h (s : G)
    rw [hRight (g * h) s, hRight h s, zero_add, smul_zero, zero_add] at he
    exact he.symm
  have h₁ (g h : G) (s : S) : c (g * (s : G), h) = c (g, h) := by
    let t : S := ⟨h⁻¹ * (s : G) * h, hS.conj_mem' s s.property h⟩
    have ht : (s : G) * h = h * (t : G) := by dsimp [t]; group
    have he := hc g (s : G) h
    rw [hRight g s, hLeft s h, add_zero, smul_zero, zero_add, ht, h₂] at he
    exact he
  have hInv (s : S) (g h : G) : (s : G) • c (g, h) = c (g, h) := by
    let t : S := ⟨g⁻¹ * (s : G) * g, hS.conj_mem' s s.property g⟩
    have ht : (s : G) * g = g * (t : G) := by dsimp [t]; group
    have he := hc (s : G) g h
    rw [hLeft s g, hLeft s (g * h), add_zero, add_zero, ht, h₁] at he
    exact he.symm
  let q := QuotientGroup.mk' S
  obtain ⟨r, hr⟩ := (QuotientGroup.mk'_surjective S).hasRightInverse
  let t (p : (G ⧸ S) × (G ⧸ S)) : B.V :=
    ⟨c (r p.1, r p.2), fun s ↦ hInv s (r p.1) (r p.2)⟩
  have hValue (g h : G) : (t (q g, q h)).1 = c (g, h) := by
    let s : S := ⟨(r (q g))⁻¹ * g, QuotientGroup.eq.mp (hr (q g))⟩
    let l : S := ⟨(r (q h))⁻¹ * h, QuotientGroup.eq.mp (hr (q h))⟩
    have hs : r (q g) * (s : G) = g := by dsimp [s]; group
    have hl : r (q h) * (l : G) = h := by dsimp [l]; group
    change c (r (q g), r (q h)) = c (g, h)
    calc
      _ = c (r (q g) * (s : G), r (q h) * (l : G)) := by
        rw [h₁, h₂]
      _ = _ := by rw [hs, hl]
  refine ⟨⟨t, (mem_cocycles₂_iff t).mpr ?_⟩, hValue⟩
  intro x y z
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective S) x
  obtain ⟨h, rfl⟩ := (QuotientGroup.mk'_surjective S) y
  obtain ⟨j, rfl⟩ := (QuotientGroup.mk'_surjective S) z
  apply Subtype.ext
  change (show A from (t (q g * q h, q j)).1) + (show A from (t (q g, q h)).1) =
    g • (show A from (t (q h, q j)).1) + (show A from (t (q g, q h * q j)).1)
  rw [← q.map_mul g h, ← q.map_mul h j, hValue, hValue, hValue, hValue]
  exact hc g h j

end ManuscriptAudit.GroupTwoCocycleConjugation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GroupTwoCocycleConjugation.exists_quotient_cocycle₂
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
