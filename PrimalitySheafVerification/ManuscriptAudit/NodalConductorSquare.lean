import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.NodalConductor

/-! The affine node is the ring pullback that identifies the two split branches. -/

namespace ManuscriptAudit.NodalConductorSquare

open CategoryTheory CategoryTheory.Limits Polynomial NodalConductor

noncomputable section

universe u

variable (K : Type u) [Field K]

private abbrev Node := CommRingCat.of (coordinates K)
private abbrev Line := CommRingCat.of K[X]
private abbrev Point := CommRingCat.of K
private abbrev Branches := CommRingCat.of (K × K)

def inclusion : Node K ⟶ Line K :=
  CommRingCat.ofHom (coordinates K).val.toRingHom

def branches : Line K ⟶ Branches K :=
  CommRingCat.ofHom ((evalRingHom (1 : K)).prod (evalRingHom (-1 : K)))

def origin : Node K ⟶ Point K :=
  CommRingCat.ofHom ((evalRingHom (1 : K)).comp (inclusion K).hom)

def diagonal : Point K ⟶ Branches K :=
  CommRingCat.ofHom ((RingHom.id K).prod (RingHom.id K))

/-- Interpolation gives surjectivity to the two independent branch values. -/
theorem branches_surjective (h2 : (2 : K) ≠ 0) : Function.Surjective (branches K).hom := by
  rintro ⟨a, b⟩
  refine ⟨C ((a + b) / 2) + C ((a - b) / 2) * X, ?_⟩
  change (eval 1 _ , eval (-1) _) = (a, b)
  apply Prod.ext <;> simp <;> field_simp <;> ring

theorem branches_ker (h2 : (2 : K) ≠ 0) :
    RingHom.ker (branches K).hom = Ideal.span {x K} := by
  ext f
  rw [Ideal.mem_span_singleton, x_dvd_iff_vanishes K h2]
  change (f.eval 1, f.eval (-1)) = (0, 0) ↔ _
  simp

private theorem square_commutes :
    inclusion K ≫ branches K = origin K ≫ diagonal K := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change (f.val.eval 1, f.val.eval (-1)) = (f.val.eval 1, f.val.eval 1)
  exact Prod.ext rfl ((mem_equalBranchValues K f.val).mp
    (coordinates_le_equalBranchValues K f.property)).symm

private theorem scalar_branch_values (s : PullbackCone (branches K) (diagonal K)) (z : s.pt) :
    ((s.fst.hom z).eval 1, (s.fst.hom z).eval (-1)) = (s.snd.hom z, s.snd.hom z) :=
  congrArg (fun f : s.pt →+* (K × K) => f z) (congrArg CommRingCat.Hom.hom s.condition)

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine normalization parameters give the split nodal conductor square. -/
theorem conductor_isPullback (h2 : (2 : K) ≠ 0) :
    IsPullback (inclusion K) (origin K) (branches K) (diagonal K) := by
  let c := PullbackCone.mk (inclusion K) (origin K) (square_commutes K)
  have hc : IsLimit c := by
    fapply PullbackCone.IsLimit.mk
    · intro s
      refine CommRingCat.ofHom (s.fst.hom.codRestrict (coordinates K).toSubring ?_)
      intro z
      change s.fst.hom z ∈ coordinates K
      rw [coordinates_eq_equalBranchValues K h2, mem_equalBranchValues]
      have e := scalar_branch_values K s z
      exact (congrArg Prod.fst e).trans (congrArg Prod.snd e).symm
    · intro s
      ext z
      rfl
    · intro s
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact congrArg Prod.fst (scalar_branch_values K s z)
    · intro s m left right
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f : s.pt →+* K[X] => f z)
        (congrArg CommRingCat.Hom.hom left)
  exact IsPullback.of_isLimit hc

end

end ManuscriptAudit.NodalConductorSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductorSquare.branches_surjective,
      ``ManuscriptAudit.NodalConductorSquare.branches_ker,
      ``ManuscriptAudit.NodalConductorSquare.conductor_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
