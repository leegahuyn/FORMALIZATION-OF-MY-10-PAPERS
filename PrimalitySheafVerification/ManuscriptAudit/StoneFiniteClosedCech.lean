import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.StoneFiniteSectionExtension

/-! Continuous finite discrete Čech one-cocycles on finite closed
covers of a Stone space admit global continuous primitives. -/

namespace ManuscriptAudit.StoneFiniteClosedCech

open Set Topology

noncomputable section

variable {X D I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [TopologicalSpace D] [DiscreteTopology D]
  [AddCommGroup D] [Finite D]

private theorem isClosed_finset_union {Y I : Type*} [TopologicalSpace Y]
    (T : Finset I) (S : I → Set Y) (h : ∀ i ∈ T, IsClosed (S i)) :
    IsClosed (⋃ i ∈ T, S i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T _ ih =>
      have he : (⋃ j ∈ insert i T, S j) = S i ∪ ⋃ j ∈ T, S j := by
        ext y
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        constructor
        · rintro ⟨j, (rfl | hj), hy⟩
          · exact Or.inl hy
          · exact Or.inr ⟨j, hj, hy⟩
        · rintro (hy | ⟨j, hj, hy⟩)
          · exact ⟨i, Or.inl rfl, hy⟩
          · exact ⟨j, Or.inr hj, hy⟩
      rw [he]
      exact (h i (Finset.mem_insert_self i T)).union
        (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

private theorem continuousOn_finset_union {Y M I : Type*} [TopologicalSpace Y]
    [TopologicalSpace M] (T : Finset I) (S : I → Set Y) (p : Y → M)
    (h : ∀ i ∈ T, IsClosed (S i)) (hp : ∀ i ∈ T, ContinuousOn p (S i)) :
    ContinuousOn p (⋃ i ∈ T, S i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T _ ih =>
      have he : (⋃ j ∈ insert i T, S j) = S i ∪ ⋃ j ∈ T, S j := by
        ext y
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        constructor
        · rintro ⟨j, (rfl | hj), hy⟩
          · exact Or.inl hy
          · exact Or.inr ⟨j, hj, hy⟩
        · rintro (hy | ⟨j, hj, hy⟩)
          · exact ⟨i, Or.inl rfl, hy⟩
          · exact ⟨j, Or.inr hj, hy⟩
      rw [he]
      have hT (j : I) (hj : j ∈ T) := h j (Finset.mem_insert_of_mem hj)
      exact (hp i (Finset.mem_insert_self i T)).union_of_isClosed
        (ih hT (fun j hj ↦ hp j (Finset.mem_insert_of_mem hj)))
        (h i (Finset.mem_insert_self i T)) (isClosed_finset_union T S hT)

variable (Z : I → Set X) (closed : ∀ i, IsClosed (Z i))
variable (c : I → I → C(X, D))
variable (cocycle : ∀ i j k x, x ∈ Z i → x ∈ Z j → x ∈ Z k →
  c i j x + c j k x = c i k x)

include cocycle in
private theorem diagonal_zero (i : I) {x : X} (hx : x ∈ Z i) : c i i x = 0 := by
  have h := cocycle i i i x hx hx hx
  exact add_right_cancel (show c i i x + c i i x = 0 + c i i x by simpa only [zero_add] using h)

include cocycle in
private theorem reverse_sign (i j : I) {x : X} (hi : x ∈ Z i) (hj : x ∈ Z j) :
    -c i j x = c j i x := by
  have h := cocycle i j i x hi hj hi
  rw [diagonal_zero Z c cocycle i hi] at h
  apply add_left_cancel (a := c i j x)
  rw [add_neg_cancel, h]

include closed cocycle in
set_option maxHeartbeats 1800000 in
private theorem solve_finset (T : Finset I) :
    ∃ b : I → C(X, D), ∀ i ∈ T, ∀ j ∈ T, ∀ x, x ∈ Z i → x ∈ Z j →
      b j x - b i x = c i j x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨fun _ ↦ ContinuousMap.const X 0, by simp⟩
  | @insert k T hk ih =>
    obtain ⟨b, hb⟩ := ih
    let W (i : I) := Z i ∩ Z k
    let U : Set X := ⋃ i ∈ T, W i
    have hW (i : I) : IsClosed (W i) := (closed i).inter (closed k)
    have hU : IsClosed U := isClosed_finset_union T W (fun i _ ↦ hW i)
    have hidx (x : U) : ∃ i ∈ T, x.val ∈ W i := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
      obtain ⟨hiT, hx⟩ := Set.mem_iUnion.mp hi
      exact ⟨i, hiT, hx⟩
    choose idx idxT idxW using hidx
    let p : U → D := fun x ↦ b (idx x) x + c (idx x) k x
    have hEq (i : I) (hi : i ∈ T) (x : U) (hx : x.val ∈ W i) :
        p x = b i x + c i k x := by
      have h := hb i hi (idx x) (idxT x) x hx.1 (idxW x).1
      change b (idx x) x + c (idx x) k x = b i x + c i k x
      rw [sub_eq_iff_eq_add.mp h]
      have hc := cocycle i (idx x) k x hx.1 (idxW x).1 hx.2
      calc
        _ = b i x + (c i (idx x) x + c (idx x) k x) := by abel
        _ = _ := congrArg (fun z ↦ b i x + z) hc
    let W' (i : I) : Set U := (Subtype.val : U → X) ⁻¹' W i
    have hp : Continuous p := by
      apply continuousOn_univ.mp
      have hCover : (⋃ i ∈ T, W' i) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        exact Set.mem_iUnion.mpr ⟨idx x, Set.mem_iUnion.mpr ⟨idxT x, idxW x⟩⟩
      rw [← hCover]
      apply continuousOn_finset_union T W' p
      · intro i _
        exact (hW i).preimage continuous_subtype_val
      · intro i hi
        have hf : Continuous (fun x : U ↦ b i x.val + c i k x.val) :=
          (continuous_of_discreteTopology : Continuous (fun q : D × D ↦ q.1 + q.2)).comp
            (((b i).continuous.comp continuous_subtype_val).prodMk
              ((c i k).continuous.comp continuous_subtype_val))
        exact hf.continuousOn.congr (fun x hx ↦ hEq i hi x hx)
    obtain ⟨g, hg⟩ := StoneFiniteSectionExtension.exists_extension U hU ⟨p, hp⟩
    have hG (i : I) (hi : i ∈ T) (x : X) (hx : x ∈ W i) :
        g x = b i x + c i k x := by
      let z : U := ⟨x, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx⟩⟩⟩
      exact (hg z).trans (hEq i hi z hx)
    let b' : I → C(X, D) := fun i ↦ if i = k then g else b i
    refine ⟨b', ?_⟩
    intro i hi j hj x hxi hxj
    rcases Finset.mem_insert.mp hi with hik | hiT
    · subst i
      rcases Finset.mem_insert.mp hj with hjk | hjT
      · subst j
        rw [sub_self, diagonal_zero Z c cocycle k hxi]
      · have hj' : j ≠ k := fun h ↦ hk (h ▸ hjT)
        simp only [b', if_pos rfl, if_neg hj']
        rw [← reverse_sign Z c cocycle j k hxj hxi, hG j hjT x ⟨hxj, hxi⟩]
        abel
    · have hi' : i ≠ k := fun h ↦ hk (h ▸ hiT)
      rcases Finset.mem_insert.mp hj with hjk | hjT
      · subst j
        simp only [b', if_pos rfl, if_neg hi']
        rw [hG i hiT x ⟨hxi, hxj⟩]
        abel
      · have hj' : j ≠ k := fun h ↦ hk (h ▸ hjT)
        simpa only [b', if_neg hi', if_neg hj'] using hb i hiT j hjT x hxi hxj

include closed cocycle in
/-- The cocycle is a literal difference of sections on all pairwise closed intersections. -/
theorem exists_trivialization [Finite I] :
    ∃ b : I → C(X, D), ∀ i j x, x ∈ Z i → x ∈ Z j → b j x - b i x = c i j x := by
  classical
  letI := Fintype.ofFinite I
  obtain ⟨b, hb⟩ := solve_finset Z closed c cocycle (Finset.univ : Finset I)
  exact ⟨b, fun i j ↦ hb i (Finset.mem_univ i) j (Finset.mem_univ j)⟩

end
end ManuscriptAudit.StoneFiniteClosedCech

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.StoneFiniteClosedCech.exists_trivialization
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
