import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Maps.Basic

/-!
# Trace on functions for a topological two-sheeted quotient

The sum over a point and its involutive translate descends continuously.
For two-torsion coefficients the kernel is exactly the pullback of
functions on the quotient. A split cover has surjective trace.
-/

namespace ManuscriptAudit.DoubleCoverTopologicalTrace

open Topology

noncomputable section

variable {V U M : Type*} [TopologicalSpace V] [TopologicalSpace U] [TopologicalSpace M]
variable [AddCommGroup M] [IsTopologicalAddGroup M]
variable (p : C(V, U)) (σ : C(V, V))
variable (hquot : IsQuotientMap p) (hinvol : Function.Involutive σ)
variable (hfiber : ∀ x y : V, p y = p x → y = x ∨ y = σ x)

private def traceFunction (s : C(V, M)) (y : U) : M :=
  s (Function.surjInv hquot.surjective y) + s (σ (Function.surjInv hquot.surjective y))

include hinvol hfiber

theorem traceFunction_on_fiber (s : C(V, M)) (x : V) :
    traceFunction p σ hquot s (p x) = s x + s (σ x) := by
  let y := Function.surjInv hquot.surjective (p x)
  have hy : p y = p x := Function.surjInv_eq hquot.surjective (p x)
  change s y + s (σ y) = s x + s (σ x)
  rcases hfiber x y hy with h | h
  · rw [h]
  · rw [h, hinvol x, add_comm]

private def traceContinuous (s : C(V, M)) : C(U, M) where
  toFun := traceFunction p σ hquot s
  continuous_toFun := by
    apply hquot.continuous_iff.mpr
    have he : traceFunction p σ hquot s ∘ p = fun x => s x + s (σ x) :=
      funext (traceFunction_on_fiber p σ hquot hinvol hfiber s)
    rw [he]
    exact s.continuous.add (s.continuous.comp σ.continuous)

/-- Trace is a homomorphism of the groups of continuous functions. -/
def trace : C(V, M) →+ C(U, M) where
  toFun := traceContinuous p σ hquot hinvol hfiber
  map_zero' := by
    apply ContinuousMap.ext
    intro y
    change (0 : M) + 0 = 0
    exact zero_add _
  map_add' s t := by
    apply ContinuousMap.ext
    intro y
    change (s _ + t _) + (s _ + t _) = (s _ + s _) + (t _ + t _)
    abel

theorem trace_apply (s : C(V, M)) (x : V) :
    trace p σ hquot hinvol hfiber s (p x) = s x + s (σ x) :=
  traceFunction_on_fiber p σ hquot hinvol hfiber s x

theorem trace_natural {V' U' : Type*} [TopologicalSpace V'] [TopologicalSpace U']
    (p' : C(V', U')) (σ' : C(V', V')) (hq' : IsQuotientMap p')
    (hi' : Function.Involutive σ')
    (hf' : ∀ x y : V', p' y = p' x → y = x ∨ y = σ' x)
    (g : C(V', V)) (f : C(U', U))
    (hBase : ∀ x, p (g x) = f (p' x))
    (hSwap : ∀ x, g (σ' x) = σ (g x)) (s : C(V, M)) :
    trace p' σ' hq' hi' hf' (s.comp g) = (trace p σ hquot hinvol hfiber s).comp f := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hq'.surjective y
  rw [trace_apply p' σ' hq' hi' hf']
  change s (g x) + s (g (σ' x)) = trace p σ hquot hinvol hfiber s (f (p' x))
  rw [← hBase x, trace_apply p σ hquot hinvol hfiber, hSwap x]

theorem trace_eq_zero_iff_descends (hover : ∀ x, p (σ x) = p x)
    (htwo : ∀ m : M, m + m = 0) (s : C(V, M)) :
    trace p σ hquot hinvol hfiber s = 0 ↔ ∃ t : C(U, M), t.comp p = s := by
  constructor
  · intro h
    have hinv (x : V) : s (σ x) = s x := by
      have hs := congrArg (fun t : C(U, M) => t (p x)) h
      rw [trace_apply p σ hquot hinvol hfiber] at hs
      exact add_left_cancel (hs.trans (htwo (s x)).symm)
    let t : U → M := fun y => s (Function.surjInv hquot.surjective y)
    have hcomp : t ∘ p = s := by
      funext x
      let y := Function.surjInv hquot.surjective (p x)
      have hy : p y = p x := Function.surjInv_eq hquot.surjective (p x)
      change s y = s x
      rcases hfiber x y hy with h | h
      · rw [h]
      · rw [h, hinv x]
    refine ⟨⟨t, hquot.continuous_iff.mpr ?_⟩, ContinuousMap.ext (congrFun hcomp)⟩
    rw [hcomp]
    exact s.continuous
  · rintro ⟨t, rfl⟩
    apply ContinuousMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hquot.surjective y
    rw [trace_apply p σ hquot hinvol hfiber]
    change t (p x) + t (p (σ x)) = 0
    rw [hover x, htwo]

theorem trace_surjective_of_split (e : (U ⊕ U) ≃ₜ V)
    (h₀ : ∀ y, p (e (Sum.inl y)) = y)
    (hσ : ∀ y, σ (e (Sum.inl y)) = e (Sum.inr y)) :
    Function.Surjective (trace p σ hquot hinvol hfiber (M := M)) := by
  intro t
  let s₀ : C(U ⊕ U, M) := ⟨Sum.elim t (fun _ => 0),
    t.continuous.sumElim continuous_const⟩
  let s : C(V, M) := s₀.comp ⟨e.symm, e.symm.continuous⟩
  refine ⟨s, ?_⟩
  apply ContinuousMap.ext
  intro y
  calc
    _ = trace p σ hquot hinvol hfiber s (p (e (Sum.inl y))) := by rw [h₀ y]
    _ = t y := by
      rw [trace_apply p σ hquot hinvol hfiber, hσ y]
      change s₀ (e.symm (e (Sum.inl y))) + s₀ (e.symm (e (Sum.inr y))) = t y
      rw [e.symm_apply_apply, e.symm_apply_apply]
      exact add_zero _

theorem trace_zero_of_connected [PreconnectedSpace V] [TotallyDisconnectedSpace M]
    (htwo : ∀ m : M, m + m = 0) (s : C(V, M)) :
    trace p σ hquot hinvol hfiber s = 0 := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hquot.surjective y
  rw [trace_apply p σ hquot hinvol hfiber]
  rw [TotallyDisconnectedSpace.eq_of_continuous s s.continuous (σ x) x]
  exact htwo _

end

end ManuscriptAudit.DoubleCoverTopologicalTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.DoubleCoverTopologicalTrace.trace_apply,
        ``ManuscriptAudit.DoubleCoverTopologicalTrace.trace_natural,
        ``ManuscriptAudit.DoubleCoverTopologicalTrace.trace_eq_zero_iff_descends,
        ``ManuscriptAudit.DoubleCoverTopologicalTrace.trace_surjective_of_split,
        ``ManuscriptAudit.DoubleCoverTopologicalTrace.trace_zero_of_connected] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
