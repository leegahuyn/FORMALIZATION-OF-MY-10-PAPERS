# Mock2_Advanced — Part 2 감사 보고서 (lines 18851–31919, 최종 구간)

감사자: range auditor (Part K=2). 원본 `.lean`을 18851–29544까지 순차 정독, 29545–31919(`#print axioms` 블록)는 grep/집계로 스킴(아래 커버리지 로그 참조). 리포지토리 수정/빌드 없음.

## 0. 구간 구조 개요

| 구간 | 내용 | 줄 수 | 성격 |
|---|---|---|---|
| 18851–20580 | `Gamma2SixCellPolygon` 후반: 6-셀 기본영역, 컴팩트성, 조각별 매끄러운 경계, 번들 인증서 | ~1730 | **진짜 수학** |
| 20589–20789 | `Gamma2Generation`: Γ(2) = ⟨T², ST²S⁻¹, −1⟩ | ~200 | **진짜 수학** |
| 20793–21175 | `ZeroCuspThetaLift`, `GenuineGlobalThetaMultiplier`: `FullThetaCovariance` 해소 | ~380 | **진짜 수학 (핵심)** |
| 21190–21523 | a.e. 몫 위 automorphy (정/역 규약, 거의 복붙) | ~330 | 진짜(소품) |
| 21533–22885 | `GenuineSixCellWeightedL2`: θ의 6-셀 L², 단사 실현 | ~1350 | **진짜 수학** |
| 22901–23227 | `Gamma2CuspParity`: 원시열 궤도 분류 | ~330 | 진짜(작음) |
| 23236–23461 | 유한절단 래퍼, 복소→실 Lax–Milgram | ~225 | 래퍼/소품 |
| 23474–24357 | End-값 1-형식(퇴화), 산란 오류, 프로토타입 불충분, Def10 장난감 모델, 정규화 모호성 | ~880 | 오류지적·장난감 모델 |
| 24359–28903 | 원장(Ledger) 6종 + 57/174행 집계 | ~4545 | **스캐폴딩** |
| 28905–29048 | `LiteralPDFConsistencyAudit` | ~145 | 오류지적 재포장 |
| 29050–29441 | "Certification boundary" 장문 docstring | ~390 | 문서 |
| 29443–31915 | `section AxiomAudit`: `#print axioms` **2001개** | ~2475 | 스캐폴딩 |

## 2. 헤드라인 정리 (구간 내)

| # | 줄 | 식별자 / 진술(요약) | 상태 |
|---|---|---|---|
| 1 | 21156 | `fullThetaCovariance : FullThetaCovariance` — 모든 genuine 메타플렉틱 원소 a에 대해 ∃η∈S¹, θ(aτ)=η·√(cτ+d)·θ(τ) | **U** (5082의 가설을 DISCHARGE) |
| 2 | 21162–21173 | `standardThetaMultiplier`, `standardTheta_isAutomorphic`, `standardThetaMultiplier_central_value = −I` | U |
| 3 | 20785 | `gamma2_eq_closure_standard_generators : Gamma2 = Subgroup.closure {T², ST²S⁻¹, −1}` (12개 전이 항등식 + `FixedDetMatrices.induction_on`) | U |
| 4 | 22152 / 22188 | `directPositiveTheta_memLp_fundamentalMeasure` : y^{1/4}θ ∈ L²(6-셀 다각형, dxdy/y²) — 커스프 변환식 가정 없이 가우스 상계 + 역셀 높이 추정 | U |
| 5 | 22368 | `standardThetaClass_mem_positiveAutomorphicL2Submodule` (automorphy ∧ L² 동시 증명) | U |
| 6 | 22664 | `positiveRealizationLinear_injective` (다각형 제한의 단사성; `global_aeEq_of_fundamental_aeEq` 21563 사용) | U |
| 7 | 20551 | `concreteGamma2TruncationCertificate` — Prop-구조 14개 필드 전부 정리로 채움(궤도 피복 18973, 내부 유일성 18921, 컴팩트성 19453, 조각별 매끄러운 경계 20507 등) | U (DISCHARGED 인증서) |
| 8 | 19887 | `IsRegularSmoothCurvePiece.modularImage` — Möbius 작용 하 정칙곡선 보존 (Mathlib `smulFDeriv`, `hasStrictFDerivAt_smul`) | U |
| 9 | 23217 | `existsUnique_gamma2_cuspOrbit_of_isCoprime` — 원시 정수열은 3개 Γ(2) 커스프 궤도 중 정확히 하나 | U |
| 10 | 20985 / 20971 | `theta_zeroCuspLift_covariance`; `inverseHalfWeight_plainNorm_not_invariant` (PDF 역반가중 밀도 반례) | U |
| 11 | 22452 | `inverseStandardThetaAutomorphicL2Submodule_eq_bot` — PDF 역규약 + θ승수 ⇒ 0공간 | U (오류검출) |
| 12 | 23404 | `laxMilgramEquiv_apply_eq_operator` (복소 강제 연산자의 실 L-M 동치 = A) | U (래퍼급) |
| 13 | 28191 | `Section53Closure.claimEvidence` — Prop 3/4/6/7 "증거" = 장난감 모델 존재 | **T/퇴화** |
| 14 | 28870 / 28893 | `GlobalChecklistClosure.terminal`, `.evidence` (174행) | T (원장 자기일관성) |

## 3. 탈출구/신뢰기반 (구간)
- sorry/axiom/native_decide/opaque 없음(리드 확인). `Classical.choose`는 `chosenGenuineLift` (21117) 1곳 — 존재가 증명된 리프트 선택이며 군준동형 주장 없음(무해).
- `set_option maxHeartbeats 1000000` + `maxRecDepth 10000`: 25463, 25902 (50-생성자 `Fintype` 인스턴스용), `maxRecDepth 10000`: 25597, 25974, 28790, 28866 (`decide`로 카드 계산). 위험 없음, 단 비효율(`deriving Fintype` 가능).
- `decide`는 소형 유한 열거형 카드(≤174)에만 사용.
- `#print axioms` 2001개(29443–31915): 출력 결과가 파일/로그로 고정되어 있지 않아 "감사"로서의 증거력은 빌드 로그에 의존. 무해.
- 로컬 `attribute [-instance] instInnerProductSpaceRealComplex` / `[instance 2000] NormedSpace.complexToReal` (19557–19558, 20574–20576), `[local instance 10000]` (23709) — 인스턴스 우선순위 조작, 섹션 끝에서 복원함. 건전성 문제 아님.
- `namespace Function ... def Constant` (24000–24006): `CorrectedLemmas.FixedDefinition10Model.Function.Constant`를 지역 정의 — 이름 충돌 냄새.

## 4. 조건부 인증 감사 (구간)

### 4a. 구간 내 가설/인증서
| 대상 | 줄 | 분류 | 비고 |
|---|---|---|---|
| `FullThetaCovariance` (정의 5082) | 21156 | **DISCHARGED** | 앞부분 `thetaMultiplier (hfull)` 등 5120–5199의 모든 조건부 정리가 이제 무조건이 됨. 모듈 최대 성과. |
| `ConcreteGamma2TruncationCertificate` | 20520/20551 | **DISCHARGED** | 모든 필드가 증명된 정리. |
| `CorrectedDefinition3Certificate` | 26692/26706 | DISCHARGED | 위 + 패리티/궤도 분류. |
| `HasPiecewiseSmoothBoundary` (프로젝트 정의) | 19481 | 약한 정의 | 경계를 ⊆로 덮기만 함; 빈집합도 정칙 조각(20304). 문서화됨. |
| `IsAutomorphicClass`, `IsPositiveFundamentalL2` | 21208, 22281 | 정의(가설 아님) | 표준 θ가 실제로 만족함을 증명. |
| `exists_laxMilgramEquiv_with_estimates`의 `hA` (강제성) | 23449 | SUBSTANTIVE(표준) | 정상적인 정리 가정. |
| `GaugeDescentAction` 인스턴스 `trivialDescentAction` | 23670 | 퇴화 | pullback/transition 모두 항등. |
| `InsideOutsideMatch` 인스턴스 `fixedMatch` | 24255 | **퇴화(정직 표기)** | f=q, S=2+q, Ψ=z+1, G=w⁻¹; "not a claim that the unnamed mock object ... has been constructed" 명시. |

### 4b. 원장(Ledger)의 "증거" 성격
- **`KernelEvidence {P} (proof : P) : Prop | intro`** (25651, 26250에 중복 정의): 증명 색인 래퍼. `requirementEvidence` (25806, 26378)는 모든 행을 `KernelEvidence.intro`로 닫음 → "인용된 정리가 존재한다"만 커널이 확인하고, **행 ↔ 정리의 의미 대응은 사람이 고른 것이며 검사되지 않음**. 예) `.G_maassSelbergPositiveMeasure ↦ complex_I_not_nonnegativeReal` (25757, "I는 음이 아닌 실수가 아니다"), `.p05_unconditionalLabelsMatchDependencies ↦ hMass_smoothVolumeUnitData` (26321, 퇴화 모델), `.p09_halfWeightTwistNeedsBackgroundConnection ↦ curvature_zero` (26369).
- **Section53Closure** (27519–28342): Prop 3/4/6/7을 `correctedAndProved`로 표기하는데 `ClaimEvidence` (28029–28052)는 단지 `∃ T hT, MassConditionAt/HMass (smoothVolumeUnitData T hT) …`. `smoothVolumeUnitData` (12793)는 **계수 ≡ 1 (`fun _ _ _ => 1`), Lebesgue 스펙트럼 측도**인 퇴화 모델이라 질량이 m과 무관 → 논문의 Mock-I 계수에 대해 아무 것도 말하지 않음. docstring(28002–28006, 29353–29358)은 "consistency witness, not the paper's package"라고 밝히지만, **disposition 라벨은 `correctedAndProved`** → 라벨 과장(over-labelling).
- **Section54Closure**: Corollary 3.1/3.2 증거 (28689–28699, 28526–28560) = `corollary32ConcreteSpectralData` (28489: test ≡ 1, coefficient ≡ 1, Dirac δ₀) 위의 HMass — 퇴화. Corollary 3.3 = 추상 정리(`KuznetsovSpectralIdentity` 필드 소비) ∧ `Corollary33VerificationModel`(앞선 감사: geometricSide := spectralSide 동어반복 모델). Theorem 5.1 = 진짜 identity-theorem 함의 ∧ 장난감 모델 — 함의 부분은 실질적.
- **Section51Closure.ClaimEvidence** (26877–27086): Def1/Def3은 실질적. 그러나 **Def4/5/7/12/13/18의 증거는 구조체 필드 사영(A)**: Def5 = `p.re_gt_one, p.integrable`, Def7 = `h.mass_pos`, Def12 = `QGaugeVariableSheaf.factor_existsUnique`(필드 재포장), Def13 = `C.pure_tensor_rule`(필드), Def18 = `D.mass_eq`(필드), Def17 = `rfl`.
- **공허한 erratum 증거**: `definition3_unspecifiedPolygonErratum : ∃ F G : Set UpperHalfPlane, F ≠ G` (26718, ∅≠univ); `KernelErratum .equations3_20_to_3_26 := (0:ℝ)=0 ∧ 0<1 ∧ 0≠1` (24608); `.equations3_7_to_3_19` 자명 조합명제 (24605); Section52 `.lemma36 := ¬Summable (fun _ => (1:ℝ))` (27432); Section53 `.proposition15 := ¬ Nonempty (PUnit → Empty)` (28133).
- **정직한 측면(중요)**: 174행 집계 = proved 19 / correctedAndProved 110 / removedWithErratum 45. 17개 비번호 수식블록 **전부** removed (24523–24540), Lemma 3.5–3.8 및 1.2/1.3/2.1/2.2 removed (27138–27151), 핵심 실체 행(`A_concreteGamma2LiftFinal`, `B_concreteGamma2LaplacianFinal`, `E_squareRootCancellation`, `E_truncatedKuznetsovAndLimits`, `G_cuspIndexedEisenstein`, `H_eichlerShadowHarmonicityModularity` 등) removed (25536–25573). "Certification boundary" docstring (29050–29441)은 "must not be described as an unconditional formal proof of the paper's analytic claims"라고 명시. **Spt3식 순환("가설 = 결론")은 이 구간 수학부에 없음.** 단, 원장 설계상 `conditional` 상태가 없으므로(27095–27096) 조건부/장난감 결과가 `correctedAndProved`로 승격되는 구조적 편향이 있음.

### 4c. 참조 인스턴스 (구간)
- 실물: `zeroCuspLift` (20922), `standardThetaClass` (21356), `closedPolygon` (18902), `concreteGamma2TruncationCertificate` (20551) — **실제 대상**.
- 퇴화: `trivialDescentAction` (23670), `scalarMultiplicationForm` (23536, 상수 lsmul), `fixedMatch`/`data` (24249/24255), `unitCuspSeed`/`doubledCuspSeed`·디랙 측도 (24301–24323), `corollary32ConcreteSpectralData` (28489). 모두 docstring에 장난감임을 표기.

## 5. 정의 충실도 (구간)
- Γ(2) = `CongruenceSubgroup.Gamma 2`, 기본영역 = Mathlib `ModularGroup.fd/fdo/truncatedFundamentalDomain`, θ = `jacobiTheta`, 쌍곡측도 = Mathlib withDensity, a.e. 몫 = `AEEqFun`, L² = `MeasureTheory.Lp`, 미분 = `HasDerivAt/ContDiff`, Möbius 미분 = `UpperHalfPlane.smulFDeriv` → **충실**.
- genuine 메타플렉틱 원소(앞부분 3876 정의: sqrtFactor² = denom, 연속)를 그대로 사용 → 충실.
- `HasPiecewiseSmoothBoundary`/`IsRegularSmoothCurvePiece` (19469/19481): 프로젝트 자체 정의(Mathlib에 대응 개념 없음), 덮개 포함관계만 요구 — 합리적이나 약함.
- `PositiveClosedL2Space := topologicalClosure` (22590): 폐포 완비성은 정의상 자명. "closed-range 주장 아님"이라고 정직히 표기.
- End-값 1-형식 (23478): rank-1(ℂ→ℂ) 경우만, 일반 다양체 형식 아님 — 장난감.

## 6. 실질 수학 비율 (구간, 줄 기준 추정)
- 진짜 수학(비자명 증명·Mathlib 실사용): 18851–23227 + 23320–23461 ≈ **4,500줄 (≈34%)**. 이 중 정/역 규약 복붙(~300줄)과 단순 `simp` 보조정리 포함.
- 오류지적·장난감 모델·래퍼: ≈ 1,000줄 (≈8%).
- 원장·별칭·집계·문서: 24359–29441 ≈ **5,080줄 (≈39%)** — `noncomputable def xxx_proved := @Lemma` 별칭 **약 620개**(220+401), 4개 원장에 같은 정리가 반복 별칭됨.
- `#print axioms`: ≈ **2,475줄 (≈19%)**.
- ⇒ 구간 genuine math ≈ **34%** (엄격 기준 ~30%), 스캐폴딩 ≈ 58%.

## 7. 수학적 정확성 / 과장 (구간)
- 잘못된 수학 진술은 발견 못함(구간 수학부 정리는 진술=증명 내용과 일치).
- **과장 라벨**: (i) Prop 3/4/6/7, Cor 3.1/3.2의 `correctedAndProved`가 퇴화 모델 존재로만 뒷받침됨 (28029–28052, 28689–28699); (ii) `KernelEvidence` 행 매핑 일부가 주제와 무관/자명 (25757, 26321, 26369); (iii) "Proof-producing evidence … no `True` fallback" (28000–28006, 24689–24696) 문구는 형식상 참이지만, 몇몇 행의 명제 자체가 `0=0 ∧ 0<1 ∧ 0≠1`처럼 사실상 True급 (24608).
- `lemma38_smoothVolumeHMass_concreteModel_proved` (27322) docstring "A fully concrete non-atomic realization of corrected Lemma 3.8" — 계수 ≡1 모델이므로 "realization of Lemma 3.8"은 과장(단, 해당 행 자체는 removedWithErratum으로 정직).
- 긍정: `HasPiecewiseSmoothBoundary`의 약점, `PositiveClosedL2Space`가 폐포일 뿐임, `chosenGenuineLift`가 준동형 아님 등 한계를 docstring에서 스스로 밝힘.

## 8. 코드 품질 (구간)
- 18851–23461: **Mathlib 수준에 가까운 스타일**. 명확한 docstring, 작은 보조정리 분해, `Homeomorph.smul`/`MeasurePreserving` 재사용. 업스트림 후보: `gamma2_eq_closure_standard_generators`, 6-셀 Γ(2) 기본영역(`eq_of_mem_openPolygon_of_gamma2_smul_eq`, `exists_gamma2_smul_mem_closedPolygon`), `frontier_finset_iUnion_subset_iUnion_frontier`/`iInter` (20021/20035), `existsUnique_gamma2_cuspOrbit_of_isCoprime`, `IsRegularSmoothCurvePiece.modularImage`.
- 중복: `GenuineAEAutomorphicSections` vs `GenuineInverseAEAutomorphicSections` 거의 동일(~150줄×2), positive/inverse L² 보조정리 쌍, `KernelEvidence` 두 번 정의, `Disposition` 열거형 4번 재정의, 동일 정리에 대한 별칭이 4개 원장에서 반복.
- 원장 잡음: 수십 개 우주 변수 나열 (28814–28901), `.{0,0,…}` 명시 우주 인스턴스화 다수 — 유지보수 부담 큼.
- 2001개 `#print axioms` — 빌드 출력 비대화, CI 로그 의존.
- 파일 크기(31,919줄) 자체가 리뷰/업스트림 불가 수준. 분할 필요.

## 10. 구간 잠정 점수 (1–10)
| 축 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | **9** | 탈출구 0, 컴파일 확인, Classical.choose 무해 1곳. |
| 조건부 인증의 정직성(비순환성) | **7** | 수학부에 순환 없음, 45행 정직 removed, 경계 docstring 명확; 그러나 퇴화모델 기반 `correctedAndProved`와 의미검사 없는 `KernelEvidence`. |
| 수학적 실질성 | **6** | θ승수 무조건 구성·Γ(2) 생성·6-셀 L² 등 진짜 결과 ~34%; 나머지 원장. |
| 정의 충실도 | **8** | Mathlib 실제 대상 사용; 경계 정의만 프로젝트 자체·약함. |
| 코드 품질·유지보수성 | **5** | 전반부 우수, 후반부 거대 원장·복붙·#print 2001개. |
| 종합 | **6.5** | 진짜 핵심은 출판/업스트림 가치가 있으나, 구간의 2/3가 스캐폴딩. |

---

## 모듈 전체 종합 (Module-wide synthesis: 1–18850 선행 노트 + 본 구간)

**전체 genuine math 비율(줄 기준, 잠정)**: 약 **38–42%**. 산출: 1–18850은 선행 노트 기준 ~45% (θ 가우스 상계, genuine 이중피복·두-시트 분류·비분할, tent 커널 Fourier, Mathlib Tor 계산, 폐가능 그래프/LinearPMap, 많은 오류반례 — 단 상당수가 초등적) + 18851–31919 ~34%. 나머지는 추상 인증서 인터페이스 위의 조건부 조립(~20%), 장난감/퇴화 참조 인스턴스, 원장·별칭·`#print axioms`(최종 7,560줄 ≈ 파일의 24%는 순수 원장/출력).
(주의: 1–18850 비율은 선행 감사 노트에서 추정한 값이며 본 감사자가 직접 재독하지 않음.)

**모듈 전체 핵심 발견 5가지**
1. **진짜 정수론/기하 핵심이 존재하고 무조건 증명됨**: genuine Γ(2) 메타플렉틱 이중피복(3876~, sqrtFactor²=denom), 두-시트 분류(4201), 군준동형 단면 부재(4387), Γ(2) 생성정리(20785), **`FullThetaCovariance` 해소(21156) → 표준 θ 승수 무조건 구성(21162)**, y^{1/4}θ ∈ L²(6-셀 다각형)(22152), 완전한 6-셀 기본영역 인증서(20551). 프로젝트 전반에서 드문 "가설을 실제로 지운" 사례.
2. **충실한 Tor 계산**: Mathlib `CategoryTheory` Tor₁(ZMod M, ZMod N) ≅ ZMod(gcd M N) (16097, 명시적 사영분해 15756) — 다른 모듈의 "Tor := ZMod gcd" 대용물과 대조되는 진짜 결과(업스트림 후보).
3. **PDF 오류 검출이 실질적이고 정확**: Kloosterman 꼬리 발산(6484/6492), Rankin–Selberg 추론 반례(7060), 근영점 범위 역전(7098), 1/Γ(ε)→0(7141), 실수 레졸벤트 극(10106), Γ(2) 커스프 단일궤도 주장 반박(14725), damping 부등식 반박(13660), Maass 인수분해 오류(17748), 역반가중 밀도 반례(5369/20971), 역규약 θ 0공간(22452).
4. **논문의 깊은 해석적 입력은 전부 인증서 필드로 남아 있고, "구체" 거주자는 퇴화 장난감**: Kuznetsov 공식·Weil 경계(`CancellationData` 9532, `KuznetsovSpectralIdentity` 12266), Rankin–Selberg 질량 식별(`RankinSelbergToMassCertificate` 10337, 거의 순환), 스펙트럼 갭(`spectralGap_of_powerSeparation` 12704, 가설 ≈ 결론의 대우), 균일 계수 활동성(11325). 거주자: `unitCoefficientDiracData`(12002), `smoothVolumeUnitData`(12793, 계수≡1), `Corollary33VerificationModel`(13008, geometricSide := spectralSide), `corollary32ConcreteSpectralData`(28489), `FixedDefinition10Model`(23917), `HalfTwoVerificationModel`(14449). docstring은 대체로 정직하게 "verification model"이라 밝힘.
5. **원장 라벨 과장 + 거대 스캐폴딩**: 174행 중 correctedAndProved 110행, 이 중 Prop 3/4/6/7·Cor 3.1/3.2는 퇴화모델 존재만으로 `correctedAndProved`(28029–28052, 28689–28699, 그리고 선행 감사의 12928 "Concrete Propositions 3, 4, 6, and 7" 라벨); Def 4/5/7/12/13/18 증거는 필드 사영; `KernelEvidence`(25651)는 의미검사 없는 래퍼; ~620개 별칭 + 2001개 `#print axioms`. 반면 45행을 정직하게 removedWithErratum 처리하고, 경계 docstring(29050–29441)이 "논문의 무조건 증명으로 기술하지 말라"고 명시 — Spt3식 순환 "UNCONDITIONAL" 표기는 아님.

**모듈 전체 잠정 점수 (1–10)**
| 축 | 점수 | 한줄 근거 |
|---|---|---|
| 형식적 건전성 | **9** | 탈출구 0, 전체 컴파일(442 s, 0 error), Classical.choice는 무해한 추출뿐. |
| 조건부 인증의 정직성(비순환성) | **6.5** | 대부분 정직 공시·다수 removed, 그러나 거의-순환 인증서(10337, 12704)와 퇴화모델 기반 "corrected" 라벨. |
| 수학적 실질성 | **6** | θ승수·Γ(2)·Tor·tent Fourier 등 진짜 핵심이 있으나 전체의 ~40%, 그중 상당수 초등적; 논문 주정리(질량갭 등)는 미증명. |
| 정의 충실도 | **6.5** | Γ(2)/θ/메타플렉틱/Tor/Lp/LinearPMap은 Mathlib 충실; 층(LinearPresheaf), 곡률(임의 선형 d), 스펙트럼·Eisenstein·Rankin–Selberg 데이터는 추상 대용물이며 다리 없음. |
| 코드 품질·유지보수성 | **5** | 수학부 스타일 우수·업스트림 후보 다수; 31,919줄 단일 파일, 원장 중복, #print 2001개. |
| 종합 | **6.5** | 진짜 가치가 있는 핵심 + 정직한 오류지적, 그러나 논문 주장 자체는 인증되지 않았고 파일 절반 이상이 스캐폴딩/인터페이스. |

---

## 커버리지 로그 (Part 2)
- 18851–19949: Read 정독 (Gamma2SixCellPolygon: 셀, 궤도, 높이, 컴팩트성, 정칙곡선).
- 19950–21049: Read 정독 (경계 조립, 번들 인증서, Γ(2) 생성, ZeroCuspThetaLift).
- 21050–22149: Read 정독 (GlobalThetaMultiplier, AE sections ×2, WeightedL2 전반).
- 22150–23249: Read 정독 (L² 정리, submodule, 실현 단사, CuspParity).
- 23250–24369: Read 정독 (FiniteSeries, ComplexRealLaxMilgram, SmoothEndValuedOneForms, ScatteringDensityErratum, MockPrototypeUnderspecification, FixedDefinition10Model, CuspSpectralNormalizationErratum).
- 24370–25384: Read 정독 (UnnumberedFormulaLedger; 24708–25381 별칭 목록은 훑어 읽음).
- 25385–26382: Read 정독 (Section7WorkaroundLedger, P0RepairLedger).
- 26383–27101: Read 정독 (Section51Closure).
- 27102–28001: Read 정독 (Section52Closure, Section53Closure 별칭).
- 28000–28904: Read 정독 (Section53/54 ClaimEvidence, GlobalNamedClaimClosure, GlobalChecklistClosure).
- 28905–29544: Read 정독 (LiteralPDFConsistencyAudit, Certification boundary docstring, AxiomAudit 시작 100줄).
- 29545–31919: **스킴** — grep으로 `#print axioms` 이외 줄이 섹션 주석 9개와 `end AxiomAudit / end / end Mock2Adv`뿐임을 확인; `#print axioms` 2001개, 네임스페이스별 분포 집계(CorrectedLemmas 766, UnnumberedFormulaLedger 166, Section53Closure 150, …).
- 보조 확인: 5075–5100 (`FullThetaCovariance` 정의), 12793–12815 (`smoothVolumeUnitData` 정의), 18780–18850 (`closedCell`, `exists_rep_mul_gamma2`), decls JSON 집계.
