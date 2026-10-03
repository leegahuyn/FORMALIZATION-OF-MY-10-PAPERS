# Mock1_Advanced — Part 5 범위 감사 (L70001–90615, 마지막 범위)

범위 안의 선언은 934개다(theorem 784, 그중 접근자 사영 419 / def 94 / structure 55 / inductive 1). 실제 선언은 L70003–84624에 있고, **L84629–90615(5,987행)은 `#print axioms` 5,985줄뿐이다.**

**방법.** `decls_cls.json`으로 범위를 지도화한 뒤, 접근자 연속 구간을 한 줄로 접은 뷰(`view.py`/`view2.py`)를 앞에서부터 읽었다. L70001–74800은 구조체·def·비접근자 정리를 전문으로 읽었다. L74800–84628은 구조체 필드 목록, 모든 def, reference 조립부, 최종 엔드포인트를 전문으로 읽었고, 나머지는 python으로 검사했다(비접근자 정리 365개의 본문에서 전술 사용 여부를 전수 확인). 범위 밖 정의도 grep으로 찾아 해당 선언만 읽었다: `AdvancedClaimsIIRamanujanFCoefficient` L68260, 회귀 구간 L25177–25230, `AppellLerchAnalyticData` L325, `BruinierFunkeXiCertificate` L1307, `leafStatement` L45898, `nonzeroCase` L37845, `referenceRationalOLS` L3666.

## 1. 범위 구조
| 행 | 내용 |
|---|---|
| 70001–70052 | `reference_advanced_claims_ii_entropy_paper_input_audit`(앞 범위 구조체의 인스턴스) |
| 70053–70492 | Ramanujan f 90행 엔트로피 회귀 입력: `…EntropyRegressionRow`, `…ThreeRegressorRationalOLSCertificate`, `…NinetyRowProofInput`, `…ConstructorBoundary` |
| 70493–70675 | `AdvancedClaimsIIEvidenceClass`(finiteExact/analyticBoundary/diagnosticMetadata/aggregate), 54개 요구항목 분류 `evidenceClass`, **L70578 `set_option maxHeartbeats 800000 in`** → `evidenceClass_exhaustive` |
| 70676–72157 | T1–T5 / Kernel / Exact의 finite·analytic 분리 인증서, cusp 커버리지 실패 감사, `AllPaperCusps`/`AppellLerch`/`GlobalInsideOutside` ProofInput과 그 ConstructorBoundary |
| 72158–72537 | Ramanujan 전용 정확계수(L-값·Euler곱·근수) ProofInput과 Boundary |
| 72538–72912 | 앞/뒤 절반 "formula closure": 참조 인증서 사실의 재진술(`…BackMathStatement` 3종) |
| 72913–73814 | p-adic 및 엔트로피 finite·analytic 분리, p-adic 해석범위 ProofInput, 엔트로피 점근 ProofInput |
| 73815–74462 | "Actual" Ramanujan 인증서: `…ActualAbstractCertificate`, `…ActualFullPayload`, `…ActualConcreteCertificate.ofAbstract`, `…LegacyModelIsolationCertificate`, `…ActualCertificateConstructorBoundary` |
| 74463–75900 | Back-half/AdvancedClaim formula closure, `…ChecklistFormulaLedgerCertificate`(215행 구조체와 접근자 약 40개), `…ChecklistFormulaCoverageCertificate` |
| 75901–79120 | PromptBullet/Section의 formula·statement 브리지, Section atom formula def 7개, `AdvancedClaimsIINamedPromptStatements`/`…LeafStatements`/`…StatementLeafIff`(51개 bullet × 3개의 한 줄 재수출, L77886–79120) |
| 79121–81960 | NamedPromptGroupAudit, ComprehensiveChecklistAudit, **`AdvancedClaimsIIUnconditionalCertificationReadinessCertificate`(L79726)**, Abstract/Concrete·Section 브리지, LeafDischarge, ObjectiveChecklistDischarge, Claimwise/AllPrompt/Sectionwise AtomicDischarge, `…ObjectiveFinalSynthesisCertificate`(L81692) |
| 81957–83805 | FormulaAtomicItem 행렬(def 278행), ActualInputDataMatrix, "ActualInput…Formula" def 약 40개와 "Microlocal" 결합 def |
| 83806–84628 | **최종 엔드포인트 `AdvancedClaimsIIMicrolocalCertificationReadinessCertificate`(L83806, 필드 약 50개, Type)와 `reference_advanced_claims_ii_microlocal_certification_readiness`(L84516–84624, noncomputable def)**. 이후 `end Mock1Advanced`, `end MockCert` |
| 84629–90615 | `#print axioms` 5,985줄(파일 전체 정리 목록을 기계적으로 나열) |

## 2. 헤드라인 정리 (U/C/A/T)
| # | 행 | 이름 | 내용(요약) | 상태 |
|---|---|---|---|---|
| 1 | 84516 | `reference_advanced_claims_ii_microlocal_certification_readiness` (def) | **파일의 최종 결론.** 앞서 만든 reference 인증서 약 50개를 한 구조체에 조립한 것 | T. 새 수학이 없고 모든 필드가 기존 상수다. 대상은 퇴화한 `referenceAdvancedClaimsIICompletionCertificate`와 공허한 ∀-Boundary다. `rlf_end_to_end`는 `∀ i : Fin referencePaperInstancesHRflConcrete.rationalOLS.points`인데 points = 0(`referenceRationalOLS` L3667, `{ referenceConcreteCertificate with … }`로 상속)이므로 **Fin 0 위에서 공허**하다 |
| 2 | 79843 | `reference_advanced_claims_ii_unconditional_certification_readiness` | 51 bullet, 54 요구항목, Nodup, 모든 요구항목의 `leafStatement`가 참조 인증서에서 성립 | T/A. leafStatement 자체가 참조 인증서의 필드 사실이다. 예: `completionShadowHolomorphicConsequence` ↦ `blockSum = 0 ∧ ∀x, xiFhat x = 0`(L45925), 즉 **shadow가 0** |
| 3 | 81909 | `reference_advanced_claims_ii_objective_final_synthesis` | 같은 것을 다시 조립 | T. `rlf_end_to_end`는 여기서도 Fin 0 위에서 공허 |
| 4 | 74433 | `reference_advanced_claims_ii_ramanujan_f_actual_constructor_boundary` | "∀ A : ActualAbstractCertificate, A의 필드들" | T/C-공허. A는 거주 불가로 판단됨(§3) |
| 5 | 71773 | `reference_advanced_claims_ii_ramanujan_f_appell_lerch_boundary` | ∀ I, (q^{−1/24}·f 부분합 → holomorphicPart) ∧ (= T3 블록 μ값의 가중합) ∧ ξ(완비) = scale·shadow | T(∀ I의 사영). I는 한 번도 구성되지 않음 |
| 6 | 72504 | `reference_advanced_claims_ii_ramanujan_f_exact_coefficient_boundary` | ∀ I, c(n) = C·powerTerm·L(½)·Euler곱, 근수 필터, Rademacher 공식 | T. I의 필드 사영(rootFilter만 `rcases`로 재포장) |
| 7 | 70579 | `AdvancedClaimsIIRequirement.evidenceClass_exhaustive` | 54개 요구항목이 4개 분류 리스트 중 정확히 해당 리스트에 속함 | U(사소한 부기). heartbeats 800000 상향의 원인 |
| 8 | 70924 | `advanced_claims_ii_rlf_ramanujan_f_paper_cusp_coverage_fails` | 논문의 3개 cusp 중 `one`이 2-cusp 모델에 없음 | U(사소, 정직한 부정 감사) |
| 9 | 72168 / 72178 | `advanced_claims_ii_ramanujan_f_coefficient_two` / `…_not_unit_exact_model` | f의 c(2) = −2 (`decide`), 따라서 f ≠ 단위 모델 | U(작은 계산) |
| 10 | 73829 | `advanced_claims_ii_ramanujan_f_paper_beta_excludes_legacy_slope` | −1/2 ∉ Table 6의 β 구간 | U(`norm_num`). §3에서 보듯 의미가 크다 |
| 11 | 71512 / 71626 / 71887 | `…t3_block_argument_difference`(u−v = −1/2, `ring`), `xi_nonzero_at`(`mul_ne_zero`), `global_coefficient_identity_at`(`ring`) | 정의를 펼친 대수 | U(사소) |
| 12 | 74066 | `AdvancedClaimsIIRamanujanFActualAbstractCertificate.full_payload_at` | "Actual" 인증서의 전체 payload | A. 거주 불가 가정 위의 사영 |

**전술 사용 통계.** 비접근자 정리 365개 중 실제 전술(`omega/simp/ring/decide/norm_num/rw/rcases`)을 쓰는 것은 28개뿐이고, **모두 L73975 이전**에 있다. **L74000–84628의 정리 전부는 `And.intro`/필드 참조만으로 된 term 조립이다.**

## 3. 조건부 인증 감사 (가장 중요)
**공통 패턴.** "ProofInput" 구조체(Type)는 빠진 해석적 정리를 필드로 진술한다. "ConstructorBoundary"(Prop)는 `∀ I : ProofInput, (I의 필드)` 꼴이고 reference 정리는 `I.field`로 채운다. 즉 **"입력이 주어지면 입력이 성립한다"는 항진명제**다. grep으로 확인한 결과, `…EntropyNinetyRowProofInput`, `…AllPaperCuspsProofInput`, `…AppellLerchAnalyticProofInput`, `…GlobalInsideOutsideProofInput`, `…ExactCoefficientProofInput`, `…PAdicAnalyticRangeProofInput`, `…EntropyAsymptoticProofInput`, `…ActualAbstractCertificate`는 **파일 어디에서도 인스턴스화되지 않는다**(binder로만 등장).

| 가설/인증서 | 행 | 분류 | 근거 |
|---|---|---|---|
| `…NinetyRowConstructorBoundary`, `…AllPaperCuspsConstructorBoundary`, `…AppellLerchConstructorBoundary`, `…T1T5AnalyticPayloadBoundary`, `…ExactCoefficientConstructorBoundary`, `…PAdicAnalyticRangeConstructorBoundary`, `…EntropyAnalyticPayloadBoundary`, `…ActualCertificateConstructorBoundary` | 70356, 71340, 71660, 71960, 72408, 73240, 73721, 74327 | **CIRCULAR(항진)** | 필드가 "∀ I, I.필드"이고 증명은 사영뿐이다 |
| `AdvancedClaimsIIRamanujanFAppellLerchAnalyticProofInput` | 71522 | **불충실(약한 제약)** | `data : AppellLerchAnalyticData`의 `mu`가 임의 함수다(L325). 실제 μ(u,v;τ)가 고정되지 않는다. T3 블록 계수 합이 1(`AdvancedClaimsIIPaperT3BlockSum = 1`)이므로 mu ≡ holomorphicPart로 두면 블록 항등식이 자명히 충족된다. ξ 연산자도 임의의 가법 사상이고 shadow `data.gz`도 임의다. 실제로 제약이 있는 것은 `qseries_limit`(f 급수의 수렴)뿐이다 |
| `…GlobalInsideOutsideProofInput` | 71824 | SUBSTANTIVE(부분) | `explicit_correction_global : ∀ n, Explicit n = Dictionary n`은 실질적인 계수 항등식이다(L1–15차만 검증됐다고 docstring이 명시). `continuationMap`은 임의 함수라 약하다 |
| `…ExactCoefficientProofInput` | 72218 | **불충실(자명 충족 가능)** | `powerTerm`, `centralLValue`, `localRows`, `rootNumber`가 임의다. globalConstant = 1, powerTerm = c(n), centralLValue = 1, localRows = [], rootNumber = 1, scalarPart = c, thetaPart = 0으로 모든 필드가 충족된다. L-값, Euler곱, Kloosterman 내용이 없다. Rademacher 인증서도 자명 충족 가능하다(Part 1 노트) |
| `…ThreeRegressorRationalOLSCertificate` / `…NinetyRowProofInput` | 70151 / 70241 | **공허한 수치 검증** | `sqrtError/logError/logAbsError/residualBound/normalEquationTolerance`에 상한이 없다. logAbsCoefficient를 α̂√n + β̂ log n + γ̂로 두면 잔차가 0이 되어 어떤 α̂도 통과한다. docstring의 "rational enclosures", "normal equations checked within explicit tolerance"는 과장이다 |
| **`AdvancedClaimsIIRamanujanFEntropyAsymptoticProofInput`** | 73588 | **SUSPECT-VACUOUS (수학적으로 거주 불가)** | 필드 `entropy_growth`는 실제 f 계수에 대해 log\|c(n)\| − (α√n + β log n + γ) → 0을 요구하고, `alpha_interval`은 α ∈ [1.81437934, 1.81439318], `beta_interval`은 β ∈ [−0.75980, −0.75969]를 요구한다(L25195–25205). Bringmann–Ono(Andrews–Dragonette) 점근 c(n) ~ (−1)^{n−1} e^{π√(n/6 − 1/144)}/(2√(n − 1/24))에 따르면, 세 회귀변수 극한의 유일성 때문에 (α, β, γ) = (π/√6 ≈ 1.2825, −1/2, −log 2)뿐이다. 따라서 구간과 모순이다. 파일 스스로 L73829에서 β 구간이 −1/2를 배제함을 증명해 두었다. ceff 구간 0.5003도 f의 참값 1/4과 다르다. Table 6의 α̂ ≈ π/√3, β̂ ≈ −3/4는 오히려 서로 다른 부분으로의 분할 q(n)의 점근에 가깝다. (Lean으로 증명한 것은 아니다. Mathlib에 해당 점근이 없다.) |
| `…ActualAbstractCertificate` / `…ActualConcreteCertificate` / `…ActualFullPayload` | 73836 / 74109 / 73990 | **SUSPECT-VACUOUS** | `entropy` 필드로 위 입력을 포함하므로 거주 불가다. 이에 관한 모든 ∀-정리(`full_payload_at`, `mathematical_payload_at`, `concrete_at` 등)는 공허하게 참이다 |
| `…PAdicAnalyticRangeProofInput` | 73085 | SUBSTANTIVE(형식상) | 실제 Ramanujan/Mahler 잔차의 mod 25 소멸을 요구한다. `rawAt/chartAt`이 임의여서 부분적으로 약하다. 충족 가능성은 미확인 |
| finite·analytic 분리 인증서 4종과 `…LegacyModelIsolationCertificate` | 70686, 70792, 72060, 72922, 73383, 74210 | DISCHARGED(사소) / 정직 | 분류 등식은 `rfl`, 나머지는 앞 범위의 `decide` 사실이다. "completionIdentityProved = false", "manifest incomplete", "extrapolated tail refutation" 같은 **정직한 부정 감사**다 |

**reference 인스턴스.** 범위 안의 reference 조립(`reference_…` 정리 43개, def 11개)은 전부 `referenceAdvancedClaimsIICompletionCertificate` 계열의 퇴화 데이터를 재사용한다. 예: Euler곱 = 1, root filter = true, Kuznetsov/Weil/L-value "accepted" 플래그, completion shadow ≡ 0, `fixedShadow.nonzeroCase := Not ((1 : Rat) = 0)`(L37845), OLS points = 0. 실제 수학 대상을 담은 것은 Ramanujan f 계수 함수뿐이다(L68260, Part 4 범위; 1 + Σ q^{n²}/(−q;q)_n²의 진짜 정의이며 16항 prefix를 `decide`로 검증). 그 해석적 성질은 모두 미인스턴스 ProofInput에 남아 있다.

## 4. 정의 충실도
- 충실: `AdvancedClaimsIIRamanujanFShiftFactor`(L71471, e^{2πi(−1/24)τ}), `…ShiftedTruncation`(q-급수 부분합 × 이동인자), `Filter.Tendsto`를 쓴 수렴 진술, `AdvancedClaimsIIThreeRegressorEntropyGrowth`(L73573), `effectiveCardyConstant` = 6(α/2)²/π².
- 불충실(프록시): μ(u,v;τ)와 ξ_k는 임의 함수/가법 사상이다. L-값, 국소 Euler 인자, 근수는 임의 실수열이다. `UpperHalfPlanePoint`는 Mathlib ℍ가 아니다. 실제 대상과 잇는 브리지 정리는 없다.
- 명명 오류: "Microlocal"(L83343–83409, L83806)은 미분방정식이나 미시국소해석과 무관하다. 그냥 원자 공식들의 ∧다. "ActualInput…Formula"는 실제 Ramanujan 입력이 아니라 퇴화 참조 인증서에 관한 진술이다(L83109–83409에 RamanujanF 언급 0회). "UnconditionalCertificationReadiness"는 참조 인증서의 레지스트리 사실 묶음에 불과하다.

## 5. 실질 수학 비중 (행 기준, 전체 20,615행)
| 범주 | 행 | 비율 |
|---|---|---|
| `#print axioms` 나열 | 5,987 | 29% |
| 접근자 사영 정리(419개) | 약 4,400 | 21% |
| Prop/Type 재진술 구조체(55개) | 약 3,230 | 16% |
| `And.intro` 재조립 정리(비접근자, 전술 없음) | 약 3,000 | 15% |
| reference 조립(정리 43 + def 11) | 약 2,600 | 13% |
| ActualInput/Section/Atom Prop def와 문서·공백 | 약 1,100 | 5% |
| 해석적 입력의 정직한 *명세*(ProofInput 8종) | 약 500 | 약 2.5% (명세일 뿐 증명은 아님) |
| **실제로 증명된 수학(전술 증명 28개와 Ramanujan 해석 def)** | **약 300** | **약 1.5%. 그마저 사소함(omega, ring, decide c(2) = −2, 구간 norm_num)** |

## 6. 수학적 오류·과장
1. **엔트로피 점근 입력의 모순**(§3): 논문 Table 6의 α̂ = 1.81439, β̂ = −0.75975를 Ramanujan f의 계수에 결부시켰다. 참값은 π/√6과 −1/2다. 파일은 −1/2 배제를 "legacy model 분리"의 근거로 쓰지만(L73815–73834), 실제로는 *논문 회귀가 f에 대해 틀렸다*는 증거다.
2. 90행 OLS의 "normal equation/enclosure 검증"은 오차 상한이 없어 공허하다(L70053–70063 docstring 과장).
3. Appell–Lerch 입력의 docstring은 "states that missing theorem exactly"라고 하지만(L71457), μ가 임의라서 실제 항등식을 진술하지 못한다.
4. "Exact coefficient/L-value 입력"도 자명 충족이 가능하다(L72218).
5. `rlf_end_to_end`(L81787, L83923)는 Fin 0 위의 공허한 "end-to-end" 진술이다.
6. 긍정적인 면: 이 범위에는 정직한 부정 진술이 많다. 예: `evidenceClass` "analyticBoundary는 Lean이 증명 필드의 귀결만 검사한다는 뜻"(L70493–70499), 플래그 false 4개(L70934–70952), cusp 커버리지 실패(L70924), unit 모델과의 구별(L72178).

## 7. 코드 품질
- 같은 사실을 6층 이상 재진술한다(BackMathStatement → ChecklistFormulaLedger(215행) → FormulaCoverage → PromptBulletBridge → SectionBridge → NamedPrompt×3 → Comprehensive → Readiness → FinalSynthesis → FormulaAtomicMatrix → ActualInputMatrix → Microlocal).
- 51개 bullet × 3개의 한 줄 재수출(L77886–79120).
- 5,985줄 `#print axioms`는 투명성 의도는 좋지만 기계적 나열이다.
- 매개변수 `(n) (x : Unit) (hn) (row) (hrow)`를 수백 개 정리에 반복한다(`x : Unit`은 무의미).
- `maxHeartbeats 800000`(L70578)은 54-생성자 enum의 filter 멤버십 `simp` 때문이며 무해하다. 다만 `decide` 또는 `List.mem_filter` 직접 증명이면 불필요하다.
- Mathlib에 기여할 만한 보조정리는 없다.

## 8. 범위 잠정 점수 (1–10)
- 형식적 건전성 **8**: 탈출구가 없고 컴파일된다. 남용은 없다.
- 조건부 인증의 정직성 **4**: 부정 감사와 evidence 분류는 정직하다. 그러나 ConstructorBoundary는 항진이고, Actual 인증서는 거주 불가이며, "Unconditional/Actual/Microlocal" 명명이 오도한다.
- 수학적 실질성 **1**: 범위 내 증명은 사소한 산술·부기뿐이다.
- 정의 충실도 **3**: f 계수와 q-이동은 실제지만 μ, ξ, L-값, Euler는 임의다.
- 코드 품질·유지보수성 **2**: 극단적 중복이고 29%가 axiom 출력 나열이다.
- 종합 **2**.

## Coverage log
- L70001–74800: 접힌 뷰로 순차 정독(구조체·def·비접근자 정리 전문, 접근자는 한 줄 요약).
- L74800–76263: `view2`로 정독(ChecklistFormulaLedger의 필드 전문과 증명, 접근자 약 40개는 요약).
- L76264–83805: 구조체 필드 목록, 모든 def 서명과 본문, reference def(L80072, 80312, 80606, 80921, 81630, 81909, 82463, 83037)를 헤더 수준으로 읽고 python으로 전수 검사했다(전술 없는 term 조립임을 확인). 전문 정독 구간: L77559–77700, L79700–79880, L80982–81110, L81692–81975, L83109–83420. 한 줄 재수출 군(L77886–79120)은 훑어봄.
- L83806–84628: 전문 정독(최종 엔드포인트).
- L84629–90615: `#print axioms` 5,985줄. grep으로 개수 확인 후 앞/뒤만 열람(훑어봄).
