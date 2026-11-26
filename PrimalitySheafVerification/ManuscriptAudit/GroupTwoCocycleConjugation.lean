import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Conjugation of a degree-two cocycle trivial on a normal subgroup

After extending the coboundary on the subgroup and subtracting it,
a two-cocycle with trivial restriction can be represented by a cocycle
vanishing on both subgroup arguments. Conjugating the resulting split
subgroup defines a one-cocycle on that subgroup.
-/

namespace ManuscriptAudit.GroupTwoCocycleConjugation

open groupCohomology

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The degree-two coboundary of an inhomogeneous one-cochain. -/
def coboundary (a : G → A) (p : G × G) : A :=
  p.1 • a p.2 - a (p.1 * p.2) + a p.1

theorem coboundary_isCocycle (a : G → A) : IsCocycle₂ (coboundary a) := by
  intro g h j
  simp only [coboundary, smul_add, smul_sub, mul_smul, mul_assoc]
  abel

private theorem sub_isCocycle {c d : G × G → A} (hc : IsCocycle₂ c) (hd : IsCocycle₂ d) :
    IsCocycle₂ (c - d) := by
  intro g h j
  simp only [Pi.sub_apply, smul_sub]
  calc
    _ = (c (g * h, j) + c (g, h)) - (d (g * h, j) + d (g, h)) := by abel
    _ = _ := by rw [hc g h j, hd g h j]; abel

/-- Extend a subgroup cochain and subtract its coboundary to normalize
a cocycle that restricts to zero in cohomology. -/
theorem exists_subtract_zeroOnSubgroup (S : Subgroup G)
    (c : G × G → A) (hc : IsCocycle₂ c)
    (h : IsCoboundary₂ (fun p : S × S ↦ c (p.1, p.2))) :
    ∃ a : G → A, IsCocycle₂ (c - coboundary a) ∧
      ∀ s t : S, (c - coboundary a) (s, t) = 0 := by
  classical
  obtain ⟨b, hb⟩ := h
  let a (g : G) : A := if hs : g ∈ S then b ⟨g, hs⟩ else 0
  have ha (s : S) : a s = b s := by simp [a, s.property]
  refine ⟨a, sub_isCocycle hc (coboundary_isCocycle a), fun s t ↦ ?_⟩
  change c (s, t) - ((s : G) • a t - a ((s : G) * (t : G)) + a s) = 0
  have hmul : a ((s : G) * (t : G)) = b (s * t) := ha (s * t)
  rw [ha s, ha t, hmul]
  exact sub_eq_zero.mpr (hb s t).symm

/-- If the cocycle vanishes on the subgroup, the difference between
the two conjugate splittings is a genuine subgroup one-cocycle. -/
theorem conjugation_isCocycle (S : Subgroup G) [hS : S.Normal]
    (c : G × G → A) (hc : IsCocycle₂ c) (hZero : ∀ s t : S, c (s, t) = 0)
    (g : G) :
    IsCocycle₁ (fun s : S ↦ c (g, g⁻¹ * (s : G) * g) - c (s, g)) := by
  intro s t
  let u : S := ⟨g⁻¹ * (s : G) * g, hS.conj_mem' s s.property g⟩
  let v : S := ⟨g⁻¹ * (t : G) * g, hS.conj_mem' t t.property g⟩
  have hgu : g * (u : G) = (s : G) * g := by dsimp [u]; group
  have hgv : g * (v : G) = (t : G) * g := by dsimp [v]; group
  have huv : (u : G) * (v : G) = g⁻¹ * ((s : G) * (t : G)) * g := by
    dsimp [u, v]
    group
  have h₁ := hc (s : G) (t : G) g
  rw [hZero s t, add_zero] at h₁
  have h₂ := hc g (u : G) (v : G)
  rw [hgu, hZero u v, smul_zero, zero_add] at h₂
  have h₃ : c ((s : G) * g, v) =
      (s : G) • c (g, v) + c (s, (t : G) * g) - c (s, g) := by
    apply eq_sub_of_add_eq
    simpa only [hgv] using (hc (s : G) g (v : G))
  change c (g, g⁻¹ * ((s : G) * (t : G)) * g) - c ((s : G) * (t : G), g) =
    (s : G) • (c (g, v) - c (t, g)) + (c (g, u) - c (s, g))
  rw [← huv, ← h₂, h₁, smul_sub, h₃]
  abel

end ManuscriptAudit.GroupTwoCocycleConjugation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GroupTwoCocycleConjugation.coboundary_isCocycle,
      ``ManuscriptAudit.GroupTwoCocycleConjugation.exists_subtract_zeroOnSubgroup,
      ``ManuscriptAudit.GroupTwoCocycleConjugation.conjugation_isCocycle] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
