# 보충 체크리스트 — 자동 탐지 밖의 순환·공허·오표기 항목 (S001–S062)

`circularity_lint.py`는 **증명 전체가 "이름 붙은 `Prop` 가설을 그대로 적용"하는 경우**만 잡습니다. 그래서 다음 경우는 놓칩니다.

- 증명이 다른 정리를 한 번 거치는 경우
- `tfae_have`로 가설들을 조립하는 경우
- 구조체 필드가 결론인 경우
- 인터페이스 자체가 만족 불가능한 경우

아래 항목은 모듈별 정독 보고서(`audit/modules/`)에서 모은 것입니다.

> **주의**: 행 번호와 판정은 에이전트 보고를 옮긴 것입니다. 단, ★ 표시는 리드가 원문 또는 Lean으로 직접 확인한 항목입니다. 처리 전에 원문을 열어 확인하세요.

처리 후에는 `- [x] … — 결과: …`로 갱신하세요. 유형 표기는 다음과 같습니다.

- `CIRC`: 순환. 가설이나 필드가 곧 결론입니다.
- `VAC`: 공허. 가설이 거짓이거나 만족 불가능합니다.
- `PROXY`: 정의를 펼치면 바로 나오는 동어반복이 논문 결과로 표기된 경우입니다.
- `LEDGER`: 원장·라벨이 실제 내용과 다릅니다.

## Spt1
- [ ] **S001** `CIRC` `EqualizerPadicSoundnessProfile` (7932)과 필드 `unitGate` (7915). `unitGate`는 X≥2에서 `X.Prime`과 동치입니다. `theorem1_fourLayer_sound_via_equalizer_padic` (7980)의 건전성 경로가 순환합니다.
- [ ] **S002** `CIRC` `thm2_1_MtA_linearization` (3936)의 둘째 결론, `MtALogInput_of_truncLog_bound` (3928), `eq4_congruence` (6867)가 C005 `MtALogInput` 계열과 같은 문제를 가집니다.
- [ ] **S003** `VAC` `theorem1_via_GK_step`와 GK 체인 전체(2623, 2977, 3082). 감사 보고에 따르면 GK 가설은 `Nat.Prime 4`를 함의합니다(C003과 함께 처리).
- [ ] **S004** `VAC` `LocalizedFailureStalkThicknessCertificate` (4857). 파일이 스스로 채울 수 없음을 증명했는데(5020), 이를 쓰는 정리(4867)가 남아 있습니다.
- [ ] **S005** `LEDGER` 인스턴스 없는 `[PadicLogTailCertificate p]`에 기대면서 "UNCONDITIONAL"로 표기한 곳(7083, 7088 → `eq4_padic_congr` 7351 등). 내용은 `sum_add_tsum_nat_add`로 쉽게 증명할 수 있으니, 증명해서 해소하세요.

## Spt2
- [ ] **S006** `CIRC` `master_equivalence` (697), `good_prime_box` (712), `curve_identity` (722). 가설 `Hder`, `Hmot`, `Hbump`, `Hsing`이 TFAE의 각 성분입니다.
- [ ] **S007** `CIRC` `CurveModel.CurveFiber` (838)의 `mot_spec`, `der_spec`. 이 때문에 `master_equivalence_curve` (984, "UNCONDITIONAL"), `etale_motivic_equality` (931), `der_eq_zero_iff_smooth` (965)가 정의를 펼치는 것만으로 성립합니다.
- [ ] **S008** `CIRC` `PaperFullFormalization.ArithmeticCurve` (2451–2501)의 필드가 곧 Thm 1.1 등입니다. 이를 사영한 2540–2778행의 "논문 정리" 약 45개도 같은 문제입니다.
- [ ] **S009** `CIRC` `corollary_3_7` (2637)은 결론의 역방향 `hnoBump_to_good`을 가설로 받습니다.
- [ ] **S010** `CIRC` `BypassCertificate.CertifiedSPT2` (4098)와 `algebraic_iff_geometric` (4101). 예전 필드를 글자 그대로 다시 쓴 것입니다.
- [ ] **S011** `LEDGER` `TautologyFreeCurve` (8802). 이름과 독스트링("without tautological bridge fields")이 사실과 다릅니다.
- [ ] **S012** `LEDGER` 체크리스트 원장이 étale·모티브·six-functor·gluing을 `nativeMathlibTheorem`으로 표기합니다(7744, 7807, 7942, 8013).

## Spt3
- [ ] **S013** `CIRC` ★ `global_certificate_conditional` (7284)은 C007/C009를 경유합니다. `#assert_spt3_certified_safe_axioms` 목록과 `spt3Boundary`에서 빼세요.
- [ ] **S014** `CIRC` `certification_iff_of_complete` (499–504)는 결론의 두 방향 `Hsound`/`Hcomplete`를 가정합니다. 머리말 486행이 스스로 경고하고 있습니다.
- [ ] **S015** `CIRC` `derived_equalizer_tfae` (333, Thm 20)는 대상과 연결되지 않은 자유 변수 `smooth`, `der`로 이루어져 있습니다.
- [ ] **S016** `CIRC` `BakerLowerBound` (4363)는 결론과 `le_trans` 한 단계 차이입니다.
- [ ] **S017** `CIRC` `JacobianEtaleBridge` (5443)가 `ec_prop2_unique_lift` (5462)에서 W와 무관한 임의 대수 A에 쓰입니다.
- [ ] **S018** `VAC` `amalgam_isSheaf` (1226), `B4_amalgam_isSheaf_conditional` (2299), `sheaf_amalgam_is_sheaf` (3098)의 가설 `hB : IsSheaf siteJ (const ℕ)`는 거짓입니다(파일 스스로 4618에서 인정). 올바른 대체판 `RepointedConst_isSheaf` (4691)로 교체하세요.
- [ ] **S019** `LEDGER` `theorem18_unconditional` (6072) / `theorem18_tfae` (6004)는 Lucas 판정법을 다시 적은 것이고, `MinFacCert`는 `Nat.prime_def_minFac` 그대로입니다. 머리말(131)과 `paperClaimStatus` (7328)는 이를 "조건부"라고 적어 서로 모순됩니다. 정직한 라벨로 통일하세요.
- [ ] **S020** `LEDGER` `PowerSeries.LogInterface` (6352)는 `logOf := 0`으로 충족됩니다. Mathlib `RingTheory/PowerSeries/Log.lean`과 Spt6 7910의 실제 결과로 교체하세요. 또 Mathlib 네임스페이스와 충돌하는 이름 `PowerSeries.logOf_mul`을 정리하세요.

## Spt4
- [ ] **S021** `CIRC` `DetectorBridge` (1022)를 쓰는 `all_detectors_agree`, `prop_3_26`.
- [ ] **S022** `CIRC` `CurveData.normalization` (1067)을 쓰는 `cd_master_identity` (1076). `CurveData.ofSES` (1799)는 부분적으로 해소합니다.
- [ ] **S023** `CIRC` `GeometricDetectors` (1828)를 쓰는 `master_identity`, `detectors_tfae`, `thm_7_1`, `cor_7_2`, `prop_7_3`, `prop_7_8`, `good_prime_geometry`, `listing2_cert`.
- [ ] **S024** `CIRC` `MasterIdentityCert` (2406)의 `.sound`, `master_full`. `arithMasterIdentityCert` (4037)는 0과 자명 fibre입니다.
- [ ] **S025** `CIRC` `DetectorAgreement` (1979)를 쓰는 `detectors_certified`.
- [ ] **S026** `CIRC` `PrincipalCoverAcyclic` (5181)의 `.computes`, 그리고 `CechComputesDerivedLowDegree` (965/977).
- [ ] **S027** `CIRC` `GoodReductionData` (2773)를 쓰는 `gate_faithful` (5650). `ofGate`에서 `minimal := True`입니다.
- [ ] **S028** `CIRC` `AbstractCurveFibre.motivic_eq_etale` (6431), `EtaleMotivicRealization` (7279), `EtaleLAdicH1.bump_eq_comb` (7833), `etale_bump_eq_motivic_jump`.
- [ ] **S029** `CIRC` `ExtRealization` (7583), `SheafCohomologyComparison` (7600), `kerComparison` (7572)는 결론 동형을 필드로 받습니다.
- [ ] **S030** `CIRC` `master_equivalence`의 `hmot` (8341). `bX, bU, bZ`가 임의의 정수열입니다.

## Spt5
- [ ] **S031** `CIRC` `derived_equalizer_tfae` (2775, "Thm A (CONDITIONAL)")는 순수 순환입니다.
- [ ] **S032** `LEDGER` `HypersurfacePresentation.projective` (3136–3146)는 숨은 가정입니다. `grounded_master_tfae` (3869)와 `cotangent_detector_tfae_uncond` (3597)가 "NO hypotheses"로 표기되어 있는데, 노드 반례를 구조적으로 배제합니다. 표기를 바로잡거나 가정을 명시하세요.
- [ ] **S033** `CIRC` `TransferData.h1EtaleZero_to_gluing` (7620), `MasterDetectors`, `HypersurfaceDetectors.etale_iff`, `FullMasterDetectors.Hmot`, `DeuringData`, `EtalePTorsionData`.
- [ ] **S034** `LEDGER` ★ `ConditionalCertificate.example5` (6562–6566)의 독스트링은 y²=x³−x / 𝔽₅를 supersingular라고 적습니다. 실제로는 a₅ = −2이고 ordinary입니다. 파일 자신의 `ecTrace_x3mx_5` (5564)와도 모순됩니다.

## Spt6
- [ ] **S035** `CIRC` `goodPrime_synchronization` (2528), `goodPrime_synchronization_extended` (3410), `curve_master_identity` (2537), `good_prime_box` (2542).
- [ ] **S036** `CIRC` `Thm93Assembly.thm93_full_tfae` (4129), `thm93_full_tfae_motivic` (4175). 가설 `Hsync`, `Hsmooth`, `Hder`, `Hcompat`가 TFAE의 각 면입니다.
- [ ] **S037** `CIRC` `Tier3.CurveDetectorData` (3330)를 쓰는 `box_from_data` (3344), `bump_zero_iff_smooth` (3352), `detector_tfae` (4113). `Tier3.SheafCohomologyData` (3384)도 같습니다.
- [ ] **S038** `CIRC` `FlasqueAcyclicityData` (4336), `DeltaCohBaseChangeData` (4621), `SiteIndependenceCertificate` (4683), `ActualSheafHShift.Certificate` (4457), `CechLowDegree.Comparison` (3528)과 `cech0_iso` (3543).
- [ ] **S039** `VAC` `GeometricSmoothnessData.uniquePadicLift_to_jacobianFullRank` (4222)는 파일 스스로 반박한 주장입니다(1255).
- [ ] **S040** `LEDGER` 형식 로그 함수방정식은 주석 처리되어 있습니다(7867–7954). 그 자리에 `formal_log_section_skipped : True := trivial` (7959)이 있는데도 원장은 `status_padicLog_formal_functional_equation := .unconditional` (6351)입니다. 주석을 풀어 증명하거나 원장을 수정하세요. `example : True := trivial` (8162–8239)도 제거하세요.
- [ ] **S041** `LEDGER` `capsule_status_classification` (6732) 등이 토이 모델 결과를 `.unconditional`, `isRepresentative = true`로 분류합니다(6304, 6391, 6360).

## Spt7
- [ ] **S042** `VAC` ★ `ModuleDepthDimensionInterface` (6709)와 `ENatDepthDimensionAPI` (6775)는 만족 불가능합니다(`audit/verification/Spt7Vacuity.lean`에서 증명). 따라서 `prop18_*` 약 160개(6929–8350), `prop18_depth_lower_bound_of_isWeaklyRegular` (7262), `ActualDepthDimensionPackage` (12990)가 공허합니다. 인터페이스를 삭제하거나 올바르게 고치세요.
- [ ] **S043** `CIRC` `equivalence_C` (11952), `equivalence_C_faithful_tfae` (11962), `equivalence_C_faithful` (12028), `equivalence_C_faithful_rh_iff_tp` (12044), `equivalence_C_faithful_localRH_tfae` (12443), `GlobalEquivalenceCBridge.rh_iff_tp` (12561/12589). "RH"와 "TP"가 임의의 `Prop`입니다.
- [ ] **S044** `CIRC` `DetTraceRadiusCertificate` (11031)를 쓰는 `prop38_radius_limit_*`. `radiusLimit := fun _ _ => True`로 채워집니다.
- [ ] **S045** `CIRC` `SheafKoszulModel` (10005, `rs : List ℕ`), `SheafKoszulChartwiseCertificate.sheafRegular_of_chartwise` (10225), `KoszulWeak/RegularAcyclicityInterface` (5291/6513).
- [ ] **S046** `CIRC` `OpenClosedWeightControl` (10802), `GrothendieckLefschetzPackage` (11136), `FiniteSupportCohomologyVanishing` (11329), `DetectorPackage` (11575), `SixFunctorData` (9286), `LocalRHWeightCertificate.pure_iff_frobenius_radius` (12379).
- [ ] **S047** `CIRC` `PadicLogBridgeCertificate` (1390), `PadicABLogTruncationCertificate` (1464), `ActualPadicLogTruncationPackage` (1584), `PadicCompletionComparison` (4192). 모두 `True`로 채워집니다.
- [ ] **S048** `LEDGER` 진짜 Tor 브리지 `abstractTorOneIsoGcd` (14746)가 `…Pending` (14620, 14961)으로 과소 표기되어 있습니다. 반면 "min 반증"(16003)은 `¬False`일 뿐입니다.

## Mock1
- [ ] **S049** `CIRC` `StabilityCertificate` (7548)를 쓰는 `theoremI8_stability_from_certificate` (7803). 필드 `alpha_invariant`가 결론이고, 인스턴스는 0개입니다.
- [ ] **S050** `CIRC` `TailCertificate.Small` (5398), `MahlerPkTubeTailCertificate.reduce` (5189)를 쓰는 `propI4_tail_higher_coefficients_in_pk_tube` (7736), 그리고 `ABLinearizationCertificate.pAdicLogLipschitzStatement` (7342). 판정 술어를 인증서가 스스로 고릅니다.
- [ ] **S051** `LEDGER` S4 추출(`S4ActualExtractionMatrix` 8312를 [I|−I]로 정의)이 `satisfiedByLean`으로 기록되어 있습니다(2204–2212). 레지스트리의 이름도 실제 선언과 맞지 않습니다(2372–2382, 2518).

## Mock1_Advanced
- [ ] **S052** `VAC` ★ `…EntropyAsymptoticProofInput` (73588)은 α ∈ [1.81438, 1.81439]를 요구하지만 실제 f(q)에서는 α = π/√6, β = −log 2입니다(수치 확인: n=3000에서 잔차 −29 대 −0.0005). 상수를 바로잡거나 삭제하세요.
- [ ] **S053** `CIRC` `coefficient_lvalue_formula_at` (29301), `NamedAnalyticBoundaryCertificate` (29829, `…Accepted := True`), `LocalEulerDecompositionCertificate`(∏L_p ≡ 1 강제), `rows_eq_reference` (29920), `crt_link` (30928).
- [ ] **S054** `CIRC` "actual Ramanujan" 입력 8종(70241, 71216, 71522, 71824, 72218, 73085, 73588, 73836)은 인스턴스화되지 않습니다. 짝인 ConstructorBoundary 8종은 "∀ I, I의 필드가 성립"이라는 항진명제입니다.
- [ ] **S055** `VAC` 퇴화 reference 체인과 최종 결론 `reference_advanced_claims_ii_microlocal_certification_readiness` (84516). `rlf_end_to_end`는 `Fin 0` 위의 진술이고, "Γ(0,4π) := 1" (28212)이며 `kuznetsovAccepted := True` (67574–67584)입니다. 헤드라인 표기에서 제외하고, 실제 f(q) (68251–68301)를 연결하거나 체인을 삭제하세요.
- [ ] **S056** `LEDGER` ★ `EnvironmentPinManifest` (12114–12212)는 v4.31.0 / `fabf563a`와 존재하지 않는 `outputs/Mock1_Integrated.lean`, `scripts/audit.ps1`을 `rfl`로 "인증"합니다. 삭제하거나 실제 값으로 바꾸세요.
- [ ] **S057** `CIRC` `GrowthStabilityBaseChangeCertificate` (25881, α를 상수함수로 둠), `UnconditionalityPolicy` (12808), `AxiomAuditCompleteness` (13027, 이름 문자열 목록일 뿐).

## Mock2
- [ ] **S058** `CIRC` `lemma6_1_covariance_restrict` (5335), `lemma6_1_qGauge_certificate` (13628). C156 `modularCovariance_restrict`와 함께 기하판 `lemma6_1` (17325)으로 대체하세요.
- [ ] **S059** `CIRC` `legacyConnectionAdmissibleGaugeAssumption` (6412)을 쓰는 `gaugeTransform_admissible` (6597), `QGaugeSPTBridge.obstruction_law` (15948)을 쓰는 `bridge_obstruction_eq_gcd` (15957), `EffectiveMassFunctional` (13923), `Mmock.PaperAnalyticInput` (10585).
- [ ] **S060** `CIRC` `GaugeAdmissible` (18475)은 결론 조건을 정의에 넣은 준순환입니다. `general_minimizer_is_retained_as_input` (20212)은 `hmin → hmin`입니다.

## QYM
- [ ] **S061** `CIRC` 교정 간극 정리 30113/30227의 가설 `HasGroundShiftedComplementCoercivity`는 간극 자체의 변분형을 다시 쓴 것입니다(준순환). `FunctionalLogic.tripleProduct_bound` (5003–5223 부근), `ennreal_liminf_gap_pos_of_coercivityProduct_forall_ge` (7278–7451 부근)도 가설이 결론의 일을 대신합니다. 표기를 "가설 의존"으로 명확히 하세요.

## Mock2_FunctionalAnalysis
- [ ] **S062** `CIRC→해소` `PhysicalGreenIdentityAt` (25478, 재진술 27863)은 형식상 순환이지만 33349/33373/33404에서 해소됩니다. 해소된 무조건판만 헤드라인에 쓰세요. 이 모듈의 나머지 가설(`HasTrivialKernel`, 트레이스 추정 등)은 실질적 외부 입력이므로 유지합니다.
