import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.StoneFiniteClosedCech
import PrimalitySheafVerification.ManuscriptAudit.StoneCechBlockDescent

/-! Continuous finite discrete Čech one-cocycles on actual compact
Stone spaces are literal continuous coboundaries. -/

namespace ManuscriptAudit.StoneCechHOne

open Set Topology
open StoneCechClopenBlocks (PairOver)
open StoneCechBlockDescent (blockImages blockImages_closed)

noncomputable section

variable {Y X D : Type*}
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
  [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
  [TopologicalSpace D] [DiscreteTopology D] [AddCommGroup D] [Finite D]

set_option maxHeartbeats 2000000 in
/-- The finite discrete cocycle on the actual fibre-pair space is the
difference between the two restrictions of one continuous section. -/
theorem exists_primitive (p : C(Y, X)) (c : C(PairOver p,D))
    (cocycle : ∀ x y z (h₁ : p x = p y) (h₂ : p y = p z),
      c ⟨(x,y),h₁⟩ + c ⟨(y,z),h₂⟩ = c ⟨(x,z),h₁.trans h₂⟩) :
    ∃ b : C(Y,D), ∀ x y (e : p x = p y), b y - b x = c ⟨(x,y),e⟩ := by
  classical
  have hDiag (y : Y) : c ⟨(y,y),rfl⟩ = 0 := by
    have h := cocycle y y y rfl rfl
    exact add_right_cancel (show c ⟨(y,y),rfl⟩ + c ⟨(y,y),rfl⟩ =
      0 + c ⟨(y,y),rfl⟩ by simpa only [zero_add] using h)
  obtain ⟨T, V, hV, hCover, hZero⟩ := StoneCechClopenBlocks.exists_blocks p c hDiag
  let I := {i : Y // i ∈ T}
  letI : Finite I := inferInstanceAs (Finite {i : Y // i ∈ T})
  let W (i : I) := V i.val
  have hW (i : I) : IsClopen (W i) := hV i.val
  have hWCover (y : Y) : ∃ i : I, y ∈ W i := by
    obtain ⟨i, hi, hy⟩ := hCover y
    exact ⟨⟨i, hi⟩, hy⟩
  have hWZero (i : I) (u v : Y) (e : p u = p v) (hu : u ∈ W i) (hv : v ∈ W i) :
      c ⟨(u,v),e⟩ = 0 := hZero i.val u v e hu hv
  let Z (i : I) := blockImages p W i
  have hZ (i : I) : IsClosed (Z i) := blockImages_closed p W hW i
  have hDesc (i j : I) := StoneCechBlockDescent.exists_descent p W hW c cocycle hWZero i j
  choose c' hc' using hDesc
  have hCocycle (i j k : I) (s : X) (hi : s ∈ Z i) (hj : s ∈ Z j) (hk : s ∈ Z k) :
      c' i j s + c' j k s = c' i k s := by
    obtain ⟨x, hx, hxs⟩ := hi
    obtain ⟨y, hy, hys⟩ := hj
    obtain ⟨z, hz, hzs⟩ := hk
    let e₁ := hxs.trans hys.symm
    let e₂ := hys.trans hzs.symm
    have h₁ : c' i j s = c ⟨(x,y),e₁⟩ := (congrArg (c' i j) hxs).symm.trans (hc' i j x y e₁ hx hy)
    have h₂ : c' j k s = c ⟨(y,z),e₂⟩ := (congrArg (c' j k) hys).symm.trans (hc' j k y z e₂ hy hz)
    have h₃ : c' i k s = c ⟨(x,z),e₁.trans e₂⟩ :=
      (congrArg (c' i k) hxs).symm.trans (hc' i k x z _ hx hz)
    rw [h₁, h₂, h₃]
    exact cocycle x y z e₁ e₂
  obtain ⟨a, ha⟩ := StoneFiniteClosedCech.exists_trivialization Z hZ c' hCocycle
  choose idx hidx using hWCover
  let b : Y → D := fun y ↦ a (idx y) (p y)
  have hB (i : I) (y : Y) (hy : y ∈ W i) : b y = a i (p y) := by
    apply sub_eq_zero.mp
    calc
      b y - a i (p y) = c' i (idx y) (p y) :=
        ha i (idx y) (p y) ⟨y, hy, rfl⟩ ⟨y, hidx y, rfl⟩
      _ = c ⟨(y,y),rfl⟩ := hc' i (idx y) y y rfl hy (hidx y)
      _ = 0 := hDiag y
  have hbc : Continuous b := by
    apply continuous_of_continuousOn_iUnion_of_isOpen
    · intro i
      exact ((a i).continuous.comp p.continuous).continuousOn.congr (fun y hy ↦ hB i y hy)
    · intro i
      exact (hW i).isOpen
    · exact Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.mpr ⟨idx y, hidx y⟩
  refine ⟨⟨b,hbc⟩, fun x y e ↦ ?_⟩
  change a (idx y) (p y) - a (idx x) (p x) = c ⟨(x,y),e⟩
  calc
    _ = a (idx y) (p x) - a (idx x) (p x) := by rw [e]
    _ = c' (idx x) (idx y) (p x) :=
      ha (idx x) (idx y) (p x) ⟨x, hidx x, rfl⟩ ⟨y, hidx y, e.symm⟩
    _ = _ := hc' (idx x) (idx y) x y e (hidx x) (hidx y)

end
end ManuscriptAudit.StoneCechHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.StoneCechHOne.exists_primitive
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
