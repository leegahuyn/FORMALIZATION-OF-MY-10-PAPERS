import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Defs
import PrimalitySheafVerification.ManuscriptAudit.GroupTwoCocycleConjugation

/-!
# Removing the mixed terms of a degree-two cocycle

Suppose a cocycle already vanishes on the normal subgroup and every
one-cocycle on that subgroup is a coboundary. Choose compatible lifts
of coset representatives. Extending them along the subgroup yields
a one-cochain whose coboundary eliminates both mixed terms.
-/

namespace ManuscriptAudit.GroupTwoCocycleConjugation

open groupCohomology

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (S : Subgroup G) [hS : S.Normal]

private def Compatible (c : G × G → A) (g : G) (a : A) : Prop :=
  ∀ s : S, c (g, g⁻¹ * (s : G) * g) - c (s, g) = (s : G) • a - a

private theorem compatible_leftMul (c : G × G → A) (hc : IsCocycle₂ c)
    (hZero : ∀ s t : S, c (s, t) = 0) (r : G) (a : A)
    (ha : Compatible S c r a) (u : S) :
    Compatible S c ((u : G) * r) ((u : G) • a + c (u, r)) := by
  intro s
  let v : S := ⟨(u : G)⁻¹ * (s : G) * (u : G), hS.conj_mem' s s.property u⟩
  let z := r⁻¹ * (v : G) * r
  have hrz : r * z = (v : G) * r := by dsimp [z]; group
  have huv : (u : G) * (v : G) = (s : G) * (u : G) := by dsimp [v]; group
  have hz : z = ((u : G) * r)⁻¹ * (s : G) * ((u : G) * r) := by
    dsimp [z, v]
    group
  have h₁ := hc (u : G) r z
  rw [hrz] at h₁
  have h₂ := hc (u : G) (v : G) r
  rw [hZero u v, add_zero, huv] at h₂
  have h₃ := hc (s : G) (u : G) r
  rw [hZero s u, add_zero] at h₃
  have h₄ := ha v
  change c (r, z) - c (v, r) = (v : G) • a - a at h₄
  have h₅ : c (u, (v : G) * r) =
      (s : G) • c (u, r) + c (s, (u : G) * r) - (u : G) • c (v, r) := by
    rw [← h₃, h₂]
    abel
  have h₆ := congrArg (fun x : A ↦ (u : G) • x) h₄
  have hAct : (u : G) • ((v : G) • a) = (s : G) • ((u : G) • a) := by
    rw [← mul_smul, huv, mul_smul]
  simp only [smul_sub, hAct] at h₆
  change c ((u : G) * r, ((u : G) * r)⁻¹ * (s : G) * ((u : G) * r)) -
      c (s, (u : G) * r) =
    (s : G) • ((u : G) • a + c (u, r)) - ((u : G) • a + c (u, r))
  rw [← hz, eq_sub_of_add_eq h₁, h₅, smul_add]
  calc
    _ = ((u : G) • c (r, z) - (u : G) • c (v, r)) +
        (s : G) • c (u, r) - c (u, r) := by abel
    _ = _ := by rw [h₆]; abel

private theorem add_coboundary_isCocycle {c : G × G → A} (hc : IsCocycle₂ c)
    (a : G → A) : IsCocycle₂ (c + coboundary a) := by
  intro g h j
  simp only [Pi.add_apply, smul_add]
  have hd := coboundary_isCocycle a g h j
  calc
    _ = (c (g * h, j) + c (g, h)) + (coboundary a (g * h, j) + coboundary a (g, h)) := by abel
    _ = _ := by rw [hc g h j, hd]; abel

set_option maxHeartbeats 1000000 in
/-- If the normal subgroup has trivial first cohomology, a two-cocycle
zero on the subgroup is cohomologous to one zero on both mixed arguments. -/
theorem exists_add_coboundary_zeroOnMixed (c : G × G → A) (hc : IsCocycle₂ c)
    (hZero : ∀ s t : S, c (s, t) = 0)
    (hOne : ∀ f : S → A, IsCocycle₁ f → IsCoboundary₁ f) :
    ∃ a : G → A, IsCocycle₂ (c + coboundary a) ∧
      (∀ (s : S) (g : G), (c + coboundary a) (s, g) = 0) ∧
      (∀ (g : G) (s : S), (c + coboundary a) (g, s) = 0) := by
  classical
  have hExists (g : G) : ∃ a, Compatible S c g a := by
    obtain ⟨a, ha⟩ := hOne _ (conjugation_isCocycle S c hc hZero g)
    exact ⟨a, fun s ↦ (ha s).symm⟩
  choose b hb using hExists
  let a (g : G) : A := if g ∈ S then 0 else b g
  have ha (g : G) : Compatible S c g (a g) := by
    by_cases hg : g ∈ S
    · intro s
      let r : S := ⟨g, hg⟩
      let t : S := ⟨g⁻¹ * (s : G) * g, hS.conj_mem' s s.property g⟩
      have h₁ := hZero r t
      have h₂ := hZero s r
      change c (g, g⁻¹ * (s : G) * g) = 0 at h₁
      change c (s, g) = 0 at h₂
      simp [a, hg, h₁, h₂]
    · simpa only [a, if_neg hg] using hb g
  let q := QuotientGroup.mk' S
  obtain ⟨repr, hrepr⟩ := (QuotientGroup.mk'_surjective S).hasRightInverse
  let r (g : G) := repr (q g)
  have hr (g : G) : q (r g) = q g := hrepr (q g)
  have hq (s : S) : q s = 1 := (QuotientGroup.eq_one_iff (s : G)).mpr s.property
  let u (g : G) : S := ⟨g * (r g)⁻¹, (QuotientGroup.eq_one_iff _).mp (show
    q (g * (r g)⁻¹) = 1 by rw [map_mul, map_inv, hr]; simp)⟩
  have hdecomp (g : G) : (u g : G) * r g = g := by
    change (g * (r g)⁻¹) * r g = g
    group
  have hrMul (s : S) (g : G) : r ((s : G) * g) = r g := by
    change repr (q ((s : G) * g)) = repr (q g)
    rw [map_mul, hq s, one_mul]
  have huMul (s : S) (g : G) : (u ((s : G) * g) : G) = (s : G) * (u g : G) := by
    change ((s : G) * g) * (r ((s : G) * g))⁻¹ = (s : G) * (g * (r g)⁻¹)
    rw [hrMul, mul_assoc]
  let a' (g : G) := (u g : G) • a (r g) + c (u g, r g)
  have haZero (s : S) : a' s = 0 := by
    have hs : r s ∈ S := (QuotientGroup.eq_one_iff _).mp (show q (r s) = 1 by rw [hr, hq s])
    let t : S := ⟨r s, hs⟩
    have hz := hZero (u s) t
    change c (u s, r s) = 0 at hz
    simp [a', a, hs, hz]
  have haMul (s : S) (g : G) : a' ((s : G) * g) = (s : G) • a' g + c (s, g) := by
    change (u ((s : G) * g) : G) • a (r ((s : G) * g)) +
        c (u ((s : G) * g), r ((s : G) * g)) =
      (s : G) • ((u g : G) • a (r g) + c (u g, r g)) + c (s, g)
    have hh := hc (s : G) (u g : G) (r g)
    rw [hZero s (u g), add_zero, hdecomp] at hh
    rw [hrMul, huMul, hh, mul_smul, smul_add]
    ac_rfl
  have hCompat (g : G) : Compatible S c g (a' g) := by
    have h := compatible_leftMul S c hc hZero (r g) (a (r g)) (ha (r g)) (u g)
    rw [hdecomp] at h
    exact h
  refine ⟨a', add_coboundary_isCocycle hc a', ?_, ?_⟩
  · intro s g
    change c (s, g) + ((s : G) • a' g - a' ((s : G) * g) + a' s) = 0
    rw [haZero s, haMul]
    abel
  · intro g s
    let t : S := ⟨g * (s : G) * g⁻¹, hS.conj_mem s s.property g⟩
    have htg : (t : G) * g = g * (s : G) := by dsimp [t]; group
    have hz : g⁻¹ * (t : G) * g = (s : G) := by dsimp [t]; group
    have h := hCompat g t
    rw [hz] at h
    change c (g, s) + (g • a' s - a' (g * (s : G)) + a' g) = 0
    rw [haZero s, smul_zero, zero_sub, ← htg, haMul]
    calc
      _ = (c (g, s) - c (t, g)) - ((t : G) • a' g - a' g) := by abel
      _ = _ := sub_eq_zero.mpr h

end ManuscriptAudit.GroupTwoCocycleConjugation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GroupTwoCocycleConjugation.exists_add_coboundary_zeroOnMixed
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
