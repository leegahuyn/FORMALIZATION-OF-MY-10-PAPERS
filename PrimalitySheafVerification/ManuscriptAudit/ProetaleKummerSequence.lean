import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerAffineLabels

/-! On the full native pro-étale site the Kummer kernel is the actual
constant sheaf of coefficient-field roots. -/

namespace ManuscriptAudit.ProetaleKummerSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleKummerPower ProetaleKummerRoots ProetaleKummerCoefficientMap
open ProetaleKummerAffineLabels

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))
  (d : ℕ)

theorem constantToRoots_locallyInjective :
    Presheaf.IsLocallyInjective (J X) (constantToRoots k d) where
  equalizerSieve_mem {U} x y h := by
    let C := U.unop.left.affineOpenCover
    let O := C.openCover
    apply ProetaleOpenCover.covering_of_covering_on_open U.unop O
    intro i
    let R := C.X i
    let g : Spec R ⟶ X := C.f i ≫ U.unop.hom
    letI : WeaklyEtale g := inferInstance
    let f := ProetaleOpenCover.coverArrow U.unop O i
    let η := constantToRoots k d
    have h' := congrArg ((roots X d).map f.op) h
    change (roots X d).map f.op (η.app U x) =
      (roots X d).map f.op (η.app U y) at h'
    rw [← NatTrans.naturality_apply η f.op x, ← NatTrans.naturality_apply η f.op y] at h'
    change η.app (op (Scheme.ProEt.mk g)) x = η.app (op (Scheme.ProEt.mk g)) y at h'
    have he : (Presheaf.equalizerSieve (X := U) x y).pullback f =
        Presheaf.equalizerSieve
          (F := (Functor.const X.ProEtᵒᵖ).obj (coefficientGroup K d))
          (X := op (Scheme.ProEt.mk g)) x y := by
      ext Y a
      rfl
    rw [he]
    exact equalizer_mem k g d x y h'

variable [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

theorem constantToRoots_locallySurjective :
    Presheaf.IsLocallySurjective (J X) (constantToRoots k d) where
  imageSieve_mem {U} s := by
    let C := U.left.affineOpenCover
    let O := C.openCover
    apply ProetaleOpenCover.covering_of_covering_on_open U O
    intro i
    rw [Presheaf.pullback_imageSieve]
    let R := C.X i
    let g : Spec R ⟶ X := C.f i ≫ U.hom
    letI : WeaklyEtale g := inferInstance
    exact image_mem k g d _

/-- The constant sheaf of coefficient roots is the actual kernel of power
on the pro-étale sheaf of units. -/
def constantKernelIso :
    (constantSheaf (J X) G).obj (coefficientGroup K d) ≅ kernel (power X d) := by
  let η := constantToRoots k d
  have hw : (J X).W η := ((J X).W_iff_isLocallyBijective η).mpr
    ⟨constantToRoots_locallyInjective k d, constantToRoots_locallySurjective k d⟩
  let P := presheafToSheaf (J X) G
  letI : IsIso (P.map η) := ((J X).W_iff η).mp hw
  let e := asIso (P.map η)
  let F : Sheaf (J X) G := ⟨roots X d, roots_isSheaf X d⟩
  exact e ≪≫ (sheafificationIso F).symm ≪≫ rootsKernelIso X d

/-- The actual kernel, units and units give the native Kummer short complex. -/
def sequence (X : Scheme.{0}) (d : ℕ) : ShortComplex (Sheaf (J X) G) :=
  ShortComplex.mk (kernel.ι (power X d)) (power X d) (kernel.condition (power X d))

include k in
/-- The genuine native Kummer sequence is short exact in invertible degree. -/
theorem sequence_shortExact : (sequence X d).ShortExact := by
  letI := power_epi k d (Nat.pos_of_ne_zero (NeZero.ne d))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (power X d))
    (inferInstanceAs (Mono (kernel.ι (power X d)))) (inferInstanceAs (Epi (power X d)))

end
end ManuscriptAudit.ProetaleKummerSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerSequence.constantToRoots_locallyInjective,
      ``ManuscriptAudit.ProetaleKummerSequence.constantToRoots_locallySurjective,
      ``ManuscriptAudit.ProetaleKummerSequence.constantKernelIso,
      ``ManuscriptAudit.ProetaleKummerSequence.sequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
