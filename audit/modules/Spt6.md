# Spt6 감사 보고서

대상: `/home/user/leegahuyn/mathlib4/PrimalitySheafVerification/Spt6.lean` (8,651행, `namespace Spt6`)
감사 방법: 원본을 1행부터 8651행까지 순서대로 전부 읽음(커버리지 로그는 맨 끝). 집계에는 `scan/Spt6.code.lean`와 `decls_cls.json`을 함께 사용함. lake/lean은 실행하지 않음.

선언 집계(decls JSON 기준): theorem 478, lemma 11, def 354, abbrev 3, structure 63, instance 11, example 35, inductive 1, 총 956개. 주석 문자 189k, 코드 문자 187k로 텍스트의 약 50%가 주석/docstring임.

---

## 1. 목적과 논문 대응

논문 #6("bump = Euler jump, good-prime synchronization, equalizer–Tor, direct-sum H¹")을 대상으로 함. 헤더 1–219행의 §-map이 논문 항목과 Lean 이름을 대응시킴. 주요 대응은 다음과 같음.
- Thm 9.3(i)⇔(ii): Hensel 게이트와 판별식/분리성 good-locus. `GoodLocus.*`, `WeierstrassGate.*`
- Thm 9.1, Prop 10.2/10.8: Tor₁(ℤ/M,ℤ/N) ≅ ℤ/gcd. `torEquivZModGcd`, `ProjRes.torFullIso`
- Lem 6.4, Prop 10.1/10.7: 등화자 핵 = (lcm), 두께 min↔max 정정, gcd–lcm 단사슬. `Additions.*`
- Prop 10.6: 직합 H¹ ≅ ⊕Λ, H⁰ = 0. 대수적 그림자(`detector_*`, `LocalizationTriangle.*`)
- Thm 6.1, Cor 6.3: bump = Δχ_mot, good-prime box. 조건부(`curve_master_identity`, `good_prime_box`, `Tier3.*`, `MotivicEuler.*`)
- Def 7.1, Prop 7.2: δcoh. `CohDimension.deltaCoh`
- §5.1, Rem 6.5/10.5: AB-선형화, p진 로그. `PadicLog.*`, `PadicLogFormal.*`, `PadicLogTransfer.*`
- §8.6–8.8: 소수 스캔, Frobenius–Tate 다항식, 초특이성. `PrimeScan.*`, `FrobeniusPointCount.*`
- §M(7525–7552행): 형식화 과정에서 찾은 논문 오류 5건(min↔max, MV 부호, module-Ext, lcm↔gcd, Thm 9.3(ii) 역방향 반례).

## 2. 헤드라인 정리 목록

| # | 행 | Lean 이름 / 진술(요약) | 상태 |
|---|---|---|---|
| 1 | 3294 | `ProjRes.torFullIso (N M) (hN : N ≠ 0) [NeZero M] : ((Tor (ModuleCat ℤ) 1).obj (ℤ/M)).obj (ℤ/N) ≅ ModuleCat.of ℤ (ZMod (gcd M N))` | **U**. Mathlib의 범주론적 `Tor`를 명시적 사영분해(`projRes` 3188, `aug_quasiIso` 3177)와 `isoLeftDerivedObj`로 계산함. 파일에서 가장 실질적인 결과임 |
| 2 | 1816 | `torEquivZModGcd : (mulLeft (M : ZMod N)).ker ≃+ ZMod (gcd N M)` (`card_ker_mulLeft` 1789) | U. 순환군 크기 논증 |
| 3 | 1189 | `GoodLocus.modPolynomial_good_locus_tfae` (monic F, deg>0): `¬p∣disc F`, `F mod p` 분리, squarefree, `IsCoprime f f'`, `discr ≠ 0`의 TFAE | U. resultant/discr 이론을 실제로 사용함 |
| 4 | 1255 | `GoodLocus.unique_lift_not_imply_unit_derivative`: X² over ℤ₂ 반례 | U. 논문 역방향 주장을 반박함 |
| 5 | 1389 | `WeierstrassGate.not_dvd_shortWeierstrass_Δ_iff_separable` (p≠2): `¬p∣Δ(E) ↔ (x³+ax+b mod p).Separable` | U |
| 6 | 315/953 | `hensel_gate_aeval`, `PrimeScan.simpleRoot_has_uniquePadicLift`, `mem_scanPrimesUpTo_iff` | U. Mathlib `hensels_lemma`의 래퍼와 스캐너 정확성 증명 |
| 7 | 2741/2830 | `Additions.range_iota_eq_ker_proj`, `coker_Phi_equiv : (ℤ/M×ℤ/N)⧸range Φ ≃+ ZMod (gcd M N)` | U |
| 8 | 1696/1883 | `zmodPiEquivOfCoprime`(유한족 CRT), `torPrimewiseDecomp` | U |
| 9 | 2236/2299 | `padicVal_pow_sub_one`(LTE), `padicVal_phi : vₚ(φⱼ(1+pᵀ)) = n+T` | U |
| 10 | 7830 | `PadicLog.ab_linearization_phi_congMod`: `∑ aⱼ log(1+φⱼ) ≡ ∑ aⱼ φⱼ (mod pᵏ)` | U. 수렴, ultrametric 추정 |
| 11 | 8095 | `PadicLogTransfer.padicLogAdditive_iff_core` | U(얕음). HasSum 유일성으로 동치를 재정식화한 것뿐임 |
| 12 | 3603/3625 | `MotivicEuler.AdditiveEuler.cone_euler`, `MotivicDeformation.deltaChi_mot` | U(얕음). `omega` 한 줄 |
| 13 | 4129 | `Thm93Assembly.thm93_full_tfae`: 6면 TFAE | **C/순환**. 2–3면 외에는 가설이 곧 결론임(§4) |
| 14 | 2528 | `goodPrime_synchronization` | **T/순환** |
| 15 | 3686 | `CohDimension.deltaCoh_eq_one (h1 : 1 ∈ cohDegrees) (h0 : 0 ∉ …)` | T. sInf 보조정리. 실제 층에 대한 입력은 없음 |

## 3. 탈출구와 신뢰 기반

- 주석과 문자열을 제거한 코드에서 `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`, `macro/elab/syntax`, `#eval/#print`는 모두 0개임(stats.json으로 확인).
- `set_option maxHeartbeats 800000`이 2곳 있음: 1895 `torReadout60Primewise`, 1915 `torReadout60`. 7872의 1000000은 주석 블록 안에 있어 효력이 없음.
- `decide`: 55회. 대부분 `FormalizationStatus` 열거형 원장 정리에 쓰이고(6728–7565), 큰 항 계산은 없음.
- `Classical.choose`는 3회로, `MotivicEuler.conePackage`(4832)에서 존재 정리로부터 데이터를 뽑는 데 쓰임. 정상적인 사용임. `nonempty_zmodPiEquivOfCoprime(...).some`(1699)도 정상임.
- `Inhabited`/`default` 트릭은 없음.
- `#print axioms` 405줄(8244–8648)은 **전부 주석 처리**되어 있어 실제 축 감사가 수행되지 않음. 일부는 존재하지 않는 이름을 참조함: `PadicLogFormal.logOf_mul`, `logOf_pow`, `Stage2Certificates.FormalCoefficientRigidity.Certificate.closed_series_eq`(8544).
- 린터 억제 5종(298–302행)과 `linter.overlappingInstances false`(6022)가 있음. 옵션은 Mathlib에 실제로 존재함을 확인함.

## 4. 조건부 인증 감사 (핵심)

### (a) 순환: 가설이 결론을 진술하거나 자명하게 함의함

- `goodPrime_synchronization` 2528: 가설 `Hgate : smooth ↔ gcd=1`, `Hder : der=0 ↔ smooth`, `Hbump : bump=0 ↔ smooth`에서 결론 `[smooth, gcd=1, der=0, bump=0].TFAE`. 가설이 TFAE를 그대로 진술함. `Tier3.goodPrime_synchronization_extended` 3410도 같은 구조임.
- `curve_master_identity` 2537, `good_prime_box` 2542, `curve_betti_identity` 2560, `curve_normalization_package` 2572: 입력 등식을 omega로 재배열할 뿐임.
- **`Thm93Assembly.thm93_full_tfae` 4129**와 `thm93_full_tfae_motivic` 4175: 진짜로 증명된 링크는 (i)⇔(ii)(A2 게이트)와 (iii)⇔(iv)(ker 모델)뿐임. 나머지는 모두 가설로 주어짐.
  - `Hsync : ¬p∣Δ(E) ↔ gcd M pk = 1`: 임의의 M, pk에 대해 곡선 판별식과 무관한 gcd를 직접 연결함.
  - `Hsmooth : ¬p∣Δ ↔ (W.b1=0 ∧ W.deltaSum=0)`: W는 곡선과 연결되지 않은 임의의 `CurveWeilCohomology`임.
  - `Hder : derived = 0 ↔ ¬p∣Δ`, `Hcompat`.
  - 따라서 "(i)–(v) 완전 동기화"는 산술 코어 두 쌍과 가설 세 개를 TFAE로 묶은 것임. docstring 4122–4128이 isolated hypotheses라고 정직하게 밝히긴 하지만, 수학적 내용은 없음.
- `Tier3.CurveDetectorData` 3330(`bump_eq_jump`, `jump_eq_graph`, `smooth_iff`, `der_iff`)에서 `box_from_data` 3344, `bump_zero_iff_smooth` 3352, `detector_tfae` 4113로 이어지는 결과는 필드 사영임. 원장도 `.packaging`으로 표시함(정직함).
- `Tier3.SheafCohomologyData` 3384(`h0_zero`, `h1_stalkSum`, 모두 ℕ)와 `deltaCoh_eq_numVisible`: 사영임.
- `Tier3Actual.FlasqueAcyclicityData` 4336: `isFlasque : Prop`가 실제 `TopCat.Sheaf.IsFlasque`와 연결되지 않은 임의의 Prop임. `dimensionShift : … → isFlasque → IsGammaAcyclic F`라서 결론을 필드로 가정함. 원장은 `.conditional`.
- `CohDimension.DeltaCohBaseChangeData` 4621: `deltaCoh_eq_of_baseChange : P → deltaCoh = deltaCoh`이고 `baseChange_available : P`임. 필드가 곧 결론임. `SiteIndependenceCertificate` 4683(`cohDegrees_eq`에서 deltaCoh 등식)도 거의 자명함.
- `ActualSheafHShift.Certificate` 4457: 실제 `Sheaf.H`를 쓰지만, 필드 `shifted_eq_sheafH`, `unshifted_eq_sheafH`(타입 등식)과 `bridge.shiftEquivSucc`, `unshiftedH0_equiv : Sheaf.H I 0 ≃ Λ`가 결론 `H¹(K) ≃ Λ`(4495)의 구성요소를 그대로 가정함. 실제 Spec ℤ 층의 인스턴스는 없음.
- `CechLowDegree.Comparison` 3528과 `CechToDerivedSS` 4586: `edge0 : Hc0 ≃+ Hd0`가 필드이고, `cech0_iso := L.edge0`(3543)는 사영임. `cech1_injective`만 짧은 실제 논증임(`injective_of_exact_zero` 3516).
- `InterfaceCapsule.GeometricSmoothnessData` 4216, `GoodOpenEtalePieceData` 4255, `MotivicC1.MotivicRealization`(`bump_eq` 3737), `Tier3.EtaleMotivicRealization` 3357: 모두 필드 사영임.
- **사실상 무내용(자명하게 inhabit 가능)인 인터페이스**
  - `FrobeniusPointCount.FrobeniusWeil` 615의 유일한 "Lefschetz 공리"는 `#E = p+1-ap`임. `ap := frobeniusTrace W`로 두면 정의상 항상 성립하므로, `ap`가 étale H¹ 위의 Frobenius trace라는 정보는 타입 어디에도 없음. 따라서 `supersingular_iff`, `charPoly_eq`의 "DERIVED"는 기하학적 내용을 담지 않음.
  - `FrobeniusData` 584도 `geomSupersingular := IsSupersingular W`, `agrees := Iff.rfl`로 자명하게 채워짐.
  - `GeometricSupersingularData` 4280은 `hasseInvariant`가 임의의 정수이고 Hasse 불변량과 연결되지 않음.

### (b) 실질적: 진짜 깊은 입력이 분리된 경우

- `MotivicC1.MotivicRealizationGen` 3784(`preservesEuler`와 `defm`만 가정, bump는 정의) 및 `EtaleCurveCohomology.WeilCohomology` 3912(SES-가법 차원 함수와 두 SES). 형태상 "상류 공리화"로는 합리적임. 다만 `Obj`, `SES`, `R`, `χ`가 전부 추상이라 실제 motive/étale 이론에 붙는 다리가 없음. 결과(`bump_eq_deltaChi` 3815, `dimH1Xp_formula` 3952)는 `omega`/`ring` 수준임.
- `PadicLogFormal.PadicLogAdditive` 8006과 `PadicLogTransfer.PadicLogAdditiveCore` 8087: p진 로그 함수방정식을 가정으로 분리함. 진짜로 열린 Mathlib 공백이고 정직하게 `.conditional`로 표시되어 있음. 다만 아래 §7의 "형식 버전은 증명됨" 주장은 거짓임.

### (c) 의심스러운 경우: 실제 의미로 인스턴스화하면 모순

- `InterfaceCapsule.GeometricSmoothnessData.uniquePadicLift_to_jacobianFullRank` 4222("unique lift → Jacobian full rank")는 파일 자신이 1255에서 반례로 거짓임을 증명한 역방향 주장임. 필드가 추상 Prop이라 Lean에서 모순은 아니지만, 원래 의미로 채우면 inhabit할 수 없음. 헤더 21행은 이를 "RETAINED (interface)"로 유지함.

### (d) 해소됨

- `Tier3Actual.injective_isGammaAcyclic` 793: 주입 층의 Γ-비순환성. Mathlib `Ext.eq_zero_of_injective`로 진짜 해소됨.
- Tor 영역: 근사(ker 모델)가 `torFullIso`로 범주론적 `Tor`에 연결됨(아래 §5).

### 참조 인스턴스와 예시

- `exampleSmoothCurve` 8138: 모든 값이 0이고 `smooth := True`임. 퇴화 인스턴스.
- `MotivicEuler.AdditiveEuler.zero` 3581: χ ≡ 0.
- `GammaDimensionShift.Certificate.closed` 5969: H := PUnit.
- `FrobeniusHasseCertificate.zeroTrace` 6111.
- `AffineFrobeniusCertificate.closed` 545: 실제 대상이긴 하지만 𝔽ₚ점 위의 Frobenius는 항등이고(505), 그 trace는 a_p와 무관함. 이름이 오해를 부름.
- `CurveWeilCohomology`, `WeilCohomology`, `MotivicRealization(Gen)`, `ActualSheafHShift.Certificate`, `FlasqueAcyclicityData`, `DeltaCohOneCertificate`에는 **실제 기하 대상을 담은 인스턴스가 하나도 없음**.

## 5. 정의 충실도

**진짜 Mathlib 대상을 쓰는 곳**
- `CategoryTheory.Tor (ModuleCat ℤ)`(2927, 3201), `ProjectiveResolution`, `QuasiIso`, `ShortExact`
- `CategoryTheory.Sheaf.H`(= Ext, `sheafCohomologyExtEquiv := Equiv.refl` 705), `Abelian.Ext`(3437, 3444)
- `TopCat.Sheaf.IsFlasque`, `skyscraperSheaf`(687), `Scheme.EllAdicCohomology`(728은 `Nonempty`만 보이므로 내용 없음)
- `WeierstrassCurve.Δ`, `Affine.Point`, `Polynomial.discr/resultant/Separable`, `hensels_lemma`, `PowerSeries.log`(7966), `Module.length`(2599), `conductor`

**근사**
- Tor의 ker 모델 `(mulLeft (M : ZMod N)).ker`: **연결 정리가 있음**. `TorComputation.kerAddEquiv` 2988과 `ProjRes.torFullIso` 3294. 다만 `Thm93Assembly.tor_equalizer_gate` 4084와 `thm93_full_tfae`는 범주론적 Tor가 아니라 근사를 사용함. "Tor₁ = 0 ↔ gcd = 1"을 실제 `Tor`로 진술한 정리는 없음(torFullIso에서 바로 따라나오지만 진술되어 있지 않음).
- H¹ 검출기와 국소화 삼각형: `skyscraperH`/`obstructionH` 2135–2143는 `P → ZMod ℓ` 또는 `PUnit`을 패턴매칭으로 **정의**한 타입임. `obstructionH_succ`는 rfl임. 실제 층 코호몰로지와의 다리는 `ActualSheafHShift.Certificate`(필드 가정)뿐이고 인스턴스는 없음.
- `SheafCohomologyData`, `CurveDetectorData`, `CurveWeilCohomology`: ℕ 숫자 필드로 된 근사이며 다리가 없음.
- `CohDimension.deltaCoh` 3656: 진짜 `Sheaf.H`를 쓰지만 `supp`가 임의의 함수라서 실제 지지집합과 연결되지 않음. δcoh = 1의 실제 인스턴스도 없음.
- `IsSupersingular := (p:ℤ) ∣ a_p` 459: 𝔽ₚ 위 타원곡선에 대해 알려진 판정법이지만, **정의**로 채택했고 기하학적 정의(Hasse 불변량)와의 다리가 없음. `frobeniusTrace`는 실제 `Nat.card W.toAffine.Point`를 사용함(좋음).
- `PrimalityShadow.sections`(2350): 층이 아니라 `Set ℕ` 술어임. `Stage2Certificates.TopCatLocalPredicateSheaf` 5762도 실제 `TopCat.subsheafToTypes`가 아니라 같은 이름의 정의임(5779).
- `FormalCoefficientRigidity.CoeffAgreement p q := p = q` 6031: 이름만 "계수 강성"일 뿐 동어반복임.

## 6. 실질 수학 내용

**실질적 증명**
- `ProjRes` 전체(3051–3305): 결측 미분을 패턴매칭으로 정의하고, `opcyclesIso`, `aug_quasiIsoAt_zero`, `chainHomologyOneIsoKer`, `rid_map_ker`, `torFullIso`를 구성함. Mathlib 호몰로지 API를 진지하게 사용함.
- `GoodLocus`(resultant 패딩 `resultant_explicit_eq_default` 1057, 기저 변환 `intCast_disc_eq` 1153)
- `card_ker_mulLeft`, `range_iota_eq_ker_proj`(셈 논증), `nonempty_zmodPiEquivOfCoprime`(Finset 귀납)
- `padicVal_pow_sub_one`(LTE), `PadicLog.norm_logOnePlus_le_radius`(ultrametric 부분합 귀납), `scanned_derivative_norm_eq_one`, `fixedPointPerms_card`

**코드 줄(비공백, 주석 제외 4,730줄) 기준 영역 분류**

| 영역 | 비율 |
|---|---|
| 실질 수학 | ≈31.5% |
| 얇은 Mathlib 래퍼 | ≈2.3% |
| 토이/새니티 모델 (4857–6257) | ≈19.9% |
| 상태 원장 (6259–7565) | ≈15.6% |
| 인터페이스/조건부 (3307–4856 대부분) | ≈16.7% |
| 근사·자명 그림자, 재진술, 예시, 헤더 | ≈14% |

원 행 기준으로는 실질 약 28%이고, `#print axioms` 주석 410줄, 헤더 304줄 등이 포함됨. **대략 실질 1/3, 스캐폴딩 2/3**.

## 7. 수학적 정확성 (과대 주장과 오표기)

1. **형식 p진 로그 함수방정식이 주석 처리되어 있음.** 7867–7954의 `/- … -/` 블록이 `one_add_X_mul_deriv_log`, `mul_deriv_logOf`, `logOf_mul`, `logOf_one`, `logOf_pow`, `logOf_mul_qp`, `logOf_pow_qp`를 통째로 감쌈. 대신 `theorem formal_log_section_skipped : True := trivial`(7959, "skipped in this Lean-4.32 build pass")이 들어 있음. 그런데도 다음 위치들은 "PROVED (uncond.)"라고 주장함.
   - 헤더 45–47
   - `status_padicLog_formal_functional_equation := .unconditional` 6351, docstring 6348–6350
   - `b1_padicLog_functional_equation_classification` 7371("representative")
   - `three_way_status_classification` 6813
   - docstring 8001–8005("The formal identity above is unconditional"), 8026–8027, 8080, 7855–7858
   - 예시 8236–8239는 `example : True := trivial`로 대체됨
2. **상태 원장이 토이 모델 결과를 "unconditional/representative"로 표시함.** 5073–5081행 docstring은 "status table later marks these as trivialSanityModel, never as representative"라고 하지만 실제로는 다음과 같음.
   - `status_uniqueLift_to_jacobian_smooth` 6304: 근거는 모든 게이트가 같은 Prop인 `UnconditionalCapsule.SmoothJacobianModel` 4869
   - `status_full_smooth_jacobian_gate_equivalence` 6308
   - `status_schemeSmooth_iff_jacobianFullRank` 6300(실제로는 인터페이스 필드)
   - `status_smooth_to_unique_lift_of_hensel_hypotheses` 6296
   - `status_trace_zero_implies_supersingular` 6391: 자기 docstring이 "the real geometric implication remains an interface-level target"이라고 함
   - `status_geometric_frobenius_characteristicPolynomial` 6387(필드 사영)
   - `status_goodOpen_to_etalePiece` 6514(토이)
   - `status_localization_triangle_sheaf` 6501(rfl 재색인)
   - `status_cech_derived_comparison` 6632(필드 데이터)
   - `status_defp_cone_uniqueness` 6653(필드)
   - `status_padicLog_fms_coefficient_rigidity` 6360(`p = q` 동어반복)

   이들 모두에 대해 `capsule_status_classification` 6732–6752, `c4_smooth_jacobian_hensel_classification` 7274, `c5_supersingular_frobenius_classification` 7293, `t1_4_*` 7435, `b4_*` 7445가 `isRepresentative = true`를 `decide`로 "증명"함. 원장은 수학적 사실이 아니라 저자가 붙인 라벨이므로 이 "감사 정리"들은 정보가 없고, 일부는 오도적임. B5/B6/B2 감사 docstring(7391–7392, 7454–7456, 7466–7468)도 "the closed model makes … unconditional"이라고 서술함.
3. 헤더 §-map 대비:
   - "§7.2 Čech = derived (deg≤1)": `cechH0`/`cechH1`(3469/3477)은 ℤ/M×ℤ/N 위의 대수일 뿐 층 Čech가 아니고, 비교는 인터페이스임.
   - "Prop 10.6 … genuine Sheaf.H of shifted complex packaged by DerivedShiftBridge": 실제 인스턴스가 없음.
   - "§10.4 T1-3 … PROVED (closed shift+alg.)": rfl 재색인임.
4. 이름이 실제보다 더 많은 것을 암시하는 경우:
   - `h1EtaleZero_to_gluing_arithmetic` 1637: 순수 CRT
   - `delta_coh_one_shadow` 2107: `Nontrivial (P → ZMod ℓ)`
   - `TopCatLocalPredicateSheaf.subsheafToTypes` 5779: Mathlib의 `subsheafToTypes`가 아님
   - `MotivicEuler.ConeUniquenessData` 4816: 콘의 유일성 자체를 필드로 둠
5. 오래된 docstring: 2854 "…`isoLeftDerivedObj`) is documented but not mechanised here"는 이후 §J(3200)에서 실제로 기계화되었음. 7957은 Lean 4.32를 언급하지만 툴체인은 v4.33.0-rc1임.
6. 플레이스홀더 예시: 8162, 8164, 8184, 8187(`torFullIso`의 (6,9) 인스턴스화 등)이 `example : True := trivial`임. `d2_padic_log_classification : True` 8108도 같음.
7. 긍정적인 점(정확성): §M의 정정 1–5는 Lean 정리로 뒷받침됨. `padicVal_thickness_intersection` 1750, `Additions.*`, `Tier3.int_module_ext_one_eq_zero` 3444, `unique_lift_not_imply_unit_derivative` 1255. 수학적으로 타당한 정정으로 보임.

## 8. 코드 품질

- 8.6k행 단일 파일에 같은 토이 레이어가 4중으로 들어 있음: `UnconditionalCapsule`, `PaperAudit`, `ClosedTargets`, `Stage2Certificates`(+`toClosedModel`). 각각 거의 같은 `sections_subset_*` 정리를 반복함(5224–5242, 5599–5617, 5727–5745, 5876–5894). `Tier3Actual`, `FrobeniusPointCount`, `MotivicC1`, `EtaleCurveCohomology`, `LocalizationTriangle`, `CohDimension`, `MotivicEuler` 네임스페이스가 여러 번 재개방됨.
- 1,300행 `FormalizationStatus` 원장과 `stage3…stage11ObjectiveProp` 체크리스트는 수학적 정보가 없음.
- 405행의 주석 처리된 `#print axioms`.
- 린터 5종 억제. `erw`(3161), `eqToIso (by congr 1)`(3300) 같은 취약 지점이 있음.
- Mathlib PR 후보:
  - `GoodLocus.not_dvd_disc_iff_separable`, `separable_iff_discr_ne_zero`, `resultant_explicit_eq_default`
  - `Tier3Actual.skyscraperSheaf_isFlasque`(AddCommGrp 스카이스크래퍼의 flasque성)
  - `zmodPiEquivOfCoprime`(단, Mathlib에 `ZMod.prodEquivPi`가 이미 있다고 1652행이 스스로 언급함)
  - ℤ/N의 명시적 `ProjectiveResolution`과 `Tor₁(ℤ/M,ℤ/N) ≅ ℤ/gcd`
  - 짧은 Weierstrass Δ의 판별식 항등식 `shortWeierstrass_Δ_eq_cubic_discr`

## 9. 컴파일 위험

- `build-logs/`, `build-evidence/`에는 Spt6 전용 컴파일 로그가 없음. `FA_QYM_13FILES_15CHECK_PIPELINE_CONTRACT_20260814.md` 96행에서 13개 필수 파일로 나열될 뿐이고, 그 문서도 "Until [FINAL_15_CHECKLIST] exists, the project remains in progress"라고 적음. 따라서 **현재 헤드에서 컴파일 여부는 미확인**임(lead의 로컬 빌드 결과를 기다려야 함).
- 7867–7954의 형식 로그 블록을 "skipped in this Lean-4.32 build pass"로 주석 처리한 것은 해당 부분이 툴체인 변경 후 컴파일되지 않아 고치지 않고 꺼 버린 정황으로 보임.
- 확인한 사항: `linter.overlappingInstances`(Mathlib/Tactic/Linter/OverlappingInstances.lean)와 `push Not`(3679)은 현재 Mathlib에 존재함. `erw`, `eqToIso (by congr 1)`, `simpa using … |>.mp` 등은 버전에 민감한 지점임.
- heartbeat 상향은 2곳(800000)으로 경미함.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 7 | sorry/axiom 0, 실제 Mathlib 대상 사용. 다만 핵심 블록을 주석 처리했고, True 플레이스홀더와 축 감사 주석이 있으며, 이 모듈의 컴파일 증거가 없음 |
| 조건부 인증의 정직성(비순환성) | 3 | 헤더는 토이를 인정하지만, 원장이 토이를 representative·unconditional로 `decide`-"증명"함. `thm93_full_tfae` 등 주요 조건부 정리가 결론을 가설로 받음. 주석 처리된 정리를 "증명됨"으로 주장함 |
| 수학적 실질성 | 6 | `torFullIso`, GoodLocus, LTE/Kummer, p진 로그 반경 추정은 진짜임. 논문의 기하/코호몰로지 주장(bump, motive, étale H¹, Spec ℤ H¹)은 하나도 증명되지 않음 |
| 정의 충실도 | 6 | Tor는 범주론적 Tor와 연결된 모범 사례임. `Sheaf.H`/Ext도 진짜임. 반면 H¹ 검출기, 곡선 코호몰로지, motive, Frobenius-Weil은 다리 없는 근사이거나 자명하게 inhabit 가능함 |
| 코드 품질·유지보수성 | 3 | 2/3가 스캐폴딩이고, 4중 토이 레이어, 1.3k행 라벨 원장, 405행 주석 감사, 오래된 docstring이 있음 |
| **종합** | **5** | 견고한 산술·호몰로지 코어(파일의 약 1/3)를 과장된 메타 원장과 순환 인터페이스가 둘러싼 형태임 |

**가장 중요한 단서**: 이 모듈의 "Thm 9.3 전체 동기화", "bump = Δχ_mot", "H¹ ≅ ⊕Λ", "Frobenius-Weil에서 유도" 같은 논문 수준 주장은 모두 결론과 동치인 가설, 자명하게 inhabit 가능한 구조체, 또는 정의로 성립하는 토이 모델에 기대고 있음. 진짜로 기계 검증된 것은 산술/대수 코어(판별식–분리성, Hensel, gcd/lcm 단사슬, 범주론적 Tor₁ ≅ ℤ/gcd, p진 valuation, 로그 추정)뿐임. 또한 형식 p진 로그 함수방정식은 주석 처리되어 존재하지 않는데도 원장과 헤더가 "unconditional, representative"로 표시함.

---

## 커버리지 로그 (원본 Spt6.lean, Read로 순차 열람)

- 1–700(헤더, imports, Hensel, Frobenius/Weil, Tier3Actual 시작)
- 700–1399(Tier3Actual, PrimeScan, GoodLocus, WeierstrassGate)
- 1400–2099(Weierstrass 끝, derangements, Spec ℤ, CRT, 두께, Tor, primewise/IC, 검출기)
- 2100–2799(국소화 삼각형, AB valuation, PrimalityShadow, 조건부 동기화, CurveInvariants, Additions)
- 2800–3499(Φ/coker, FreeResolution, TorComputation, ProjRes/torFullIso, Tier3, CechComparison)
- 3500–4199(CechLowDegree, MotivicEuler, CohDimension, MotivicC1, EtaleCurveCohomology, CRT 층, Thm93Assembly)
- 4200–4899(InterfaceCapsule, GeometricSupersingularData, FlasqueAcyclicityData, DerivedShiftBridge, ActualSheafHShift, CechToDerivedSS, CohDimension 인증서, ConePackage, UnconditionalCapsule 시작)
- 4900–5599(UnconditionalCapsule, PaperAudit, ClosedTargets, Stage2 시작)
- 5600–6399(Stage2 위상/TopCat 인증서, GammaDimensionShift, FormalCoefficientRigidity, Frobenius/Motivic/Etale 인증서, 원장 시작)
- 6400–7199(원장, stage3–11 체크리스트)
- 7200–7949(c1–c5, a1–a5, b1–b6, t1-* 분류, §M, PadicLog, PadicLogFormal 주석 블록 시작)
- 7950–8651(주석 블록 끝, formal_log_section_skipped, term_eq_coeff_log, PadicLogAdditive, PadicLogTransfer, Examples, AxiomAudit 주석)

건너뛰거나 훑기만 한 구간은 없음. 6259–7565(원장)와 8242–8649(`#print axioms` 주석)는 기계적 반복이라 빠르게 읽었지만 전부 열람함.
