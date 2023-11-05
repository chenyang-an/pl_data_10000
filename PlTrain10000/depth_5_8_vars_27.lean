variable (p1 p4 p5 p6 p0 p2 p3 : Prop)
theorem file27_47 : (((((False ∧ p1) → False) → False) → (((False ∨ p3) → False) → ((False → False) ∨ (p6 → p2)))) ∨ ((((p3 ∨ True) ∨ (p0 → p3)) ∨ ((p2 ∨ p3) ∨ (True ∨ p4))) ∧ (((p5 ∨ p3) ∧ (p4 → False)) → ((p3 → False) → False)))) := by
  apply Or.inl
  intro assump_7
  intro assump_8
  apply Or.inl
  intro assump_13
  apply False.elim assump_13


variable (p0 p4 p7 p5 p2 p3 : Prop)
theorem file27_436 : (((((True → False) → False) ∧ ((p7 → False) ∨ (p3 → False))) → (((p5 ∨ p2) ∨ (False ∨ False)) ∧ ((p0 ∨ p4) → False))) → ((((False ∨ True) → False) → False) ∨ (((p5 → True) ∧ (False → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p6 p5 p4 p3 p7 p2 p0 p1 : Prop)
theorem file27_902 : (((((p6 ∧ False) → (p6 ∧ p2)) → False) → False) ∨ ((((p2 → p4) → (p0 ∧ False)) ∧ ((p5 ∨ p7) ∧ (p3 ∨ p7))) ∧ (((p1 → False) → False) → ((p2 ∨ False) ∨ (p0 ∨ p6))))) := by
  apply Or.inl
  intro assump_1
  have assump_21 : ((p6 ∧ False) → (p6 ∧ p2)) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p5 p6 p4 p7 : Prop)
theorem file27_1494 : (((((False → p7) ∧ (p6 → p1)) ∨ ((p7 → False) → False)) ∧ (((p5 ∧ p1) → (False → False)) → False)) → ((((p5 ∨ True) → False) ∧ ((p7 ∨ p4) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_41 : ((p5 ∧ p1) → (False → False)) := by
            intro assump_22
            intro assump_23
            apply False.elim assump_23
          let assump_21 := assump_10 assump_41
          apply False.elim assump_21
      case inr assump_12 =>
        have assump_42 : ((p5 ∧ p1) → (False → False)) := by
          intro assump_34
          intro assump_35
          apply False.elim assump_35
        let assump_33 := assump_10 assump_42
        apply False.elim assump_33


variable (p6 p7 p2 p1 p3 p5 : Prop)
theorem file27_2474 : ((((((False ∧ p7) ∨ (p6 → True)) ∧ ((p1 → p2) ∧ (p2 ∧ p3))) → (((p5 ∨ True) → False) → ((False → False) ∨ (p7 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((False ∧ p7) ∨ (p6 → True)) ∧ ((p1 → p2) ∧ (p2 ∧ p3))) → (((p5 ∨ True) → False) → ((False → False) ∨ (p7 ∧ p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      case inr assump_12 =>
        cases assump_10
        case intro assump_19 assump_20 =>
          cases assump_20
          case intro assump_23 assump_24 =>
            apply Or.inl
            intro assump_29
            apply False.elim assump_29
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p1 p0 p7 p3 p2 p5 p4 : Prop)
theorem file27_3406 : (((((True ∨ p4) ∧ (p3 ∧ False)) → ((p1 ∧ p7) → (p3 → False))) → (((p3 ∨ p3) ∧ (True → False)) → ((True ∨ p0) ∨ (p4 → p5)))) ∨ ((((p7 ∧ True) ∧ (p4 ∨ p7)) → ((p5 ∨ p2) ∨ (p2 ∨ p0))) ∧ (((p5 → p2) → False) ∧ ((p4 → False) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_6 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p0 p3 p6 p4 p7 p1 p2 : Prop)
theorem file27_4005 : (((((p3 → p4) → (p3 → p2)) → ((p1 → False) → (True ∨ p2))) ∨ (((p0 ∧ p6) → (False ∧ True)) ∧ ((False → p0) ∨ (p7 ∧ False)))) ∨ ((((p3 ∧ p3) → False) → False) ∨ (((False ∧ p2) ∨ (p1 ∧ p7)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply True.intro


variable (p4 p3 p0 p6 p7 p5 : Prop)
theorem file27_4368 : ((((((False ∨ p4) ∧ (p6 ∧ p0)) → False) → (((False → p3) ∧ (False ∧ p5)) → ((True ∨ False) → (p3 → p7)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((False ∨ p4) ∧ (p6 ∧ p0)) → False) → (((False → p3) ∧ (False ∧ p5)) → ((True ∨ False) → (p3 → p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      cases assump_6
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          apply False.elim assump_19
    case inr assump_12 =>
      apply False.elim assump_12
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p2 p5 p0 p3 p1 p4 p6 : Prop)
theorem file27_5116 : ((((((p6 ∧ p1) → (p6 → True)) ∨ ((False → p0) ∧ (p0 ∧ p4))) ∨ (((p1 → False) ∨ (p2 ∨ True)) ∧ ((p2 ∧ p5) → False))) → ((((False ∧ p6) → False) ∨ ((p1 → p5) → (p3 → False))) → False)) → False) := by
  intro assump_1
  have assump_16 : ((((p6 ∧ p1) → (p6 → True)) ∨ ((False → p0) ∧ (p0 ∧ p4))) ∨ (((p1 → False) ∨ (p2 ∨ True)) ∧ ((p2 ∧ p5) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_16
  have assump_17 : (((False ∧ p6) → False) ∨ ((p1 → p5) → (p3 → False))) := by
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_7 := assump_4 assump_17
  apply False.elim assump_7


variable (p0 p3 p5 p7 p4 p1 : Prop)
theorem file27_5928 : ((((((p0 ∧ p4) ∧ (p3 ∧ p0)) → ((p1 ∧ p5) ∨ (p7 ∧ p0))) → (((p4 → p0) → False) → ((p5 ∨ True) ∨ (p1 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 ∧ p4) ∧ (p3 ∧ p0)) → ((p1 ∧ p5) ∨ (p7 ∧ p0))) → (((p4 → p0) → False) → ((p5 ∨ True) ∨ (p1 ∧ True)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p4 p0 p1 p2 p5 p6 p3 p7 : Prop)
theorem file27_6436 : (((((p0 ∧ p7) → (p0 → p0)) → False) → False) ∨ ((((p5 → False) → (p1 ∨ p7)) ∨ ((p5 → p3) → (p4 → p2))) ∨ (((p6 → False) → (p3 ∧ False)) ∨ ((p0 → p6) ∨ (p5 → True))))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p0 ∧ p7) → (p0 → p0)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_9
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p4 p3 p0 p2 : Prop)
theorem file27_6927 : ((((((p1 → False) ∧ (p2 ∧ False)) ∨ ((p4 → False) ∨ (p3 → False))) → False) ∧ ((((False → False) ∨ (p0 ∨ True)) → False) ∨ (((False → False) → False) ∧ ((p1 ∨ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_31 : ((False → False) ∨ (p0 ∨ True)) := by
        apply Or.inl
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_6 assump_31
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_17 assump_18 =>
        have assump_32 : (False → False) := by
          intro assump_25
          apply False.elim assump_25
        let assump_24 := assump_17 assump_32
        apply False.elim assump_24


variable (p5 p6 p2 p1 p7 p3 p4 : Prop)
theorem file27_7787 : ((((((p2 → p6) → False) ∨ ((p5 ∨ p7) ∨ (p4 ∨ p6))) ∧ (((p2 ∨ True) → False) ∨ ((p2 → p2) → False))) ∧ ((((p3 ∧ p4) → (p5 → True)) ∨ ((p4 → p6) ∧ (True → False))) ∨ (((p5 → False) ∨ (False ∨ p1)) ∨ ((True → False) ∧ (p2 → p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_3
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              have assump_634 : (p2 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_21 := assump_10 assump_634
              apply False.elim assump_21
            case inr assump_17 =>
              cases assump_17
              case intro assump_25 assump_26 =>
                have assump_635 : True := by
                  apply True.intro
                let assump_31 := assump_26 assump_635
                apply False.elim assump_31
          case inr assump_15 =>
            cases assump_15
            case inl assump_35 =>
              cases assump_35
              case inl assump_37 =>
                have assump_636 : (p2 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_42 := assump_10 assump_636
                apply False.elim assump_42
              case inr assump_38 =>
                cases assump_38
                case inl assump_46 =>
                  apply False.elim assump_46
                case inr assump_47 =>
                  have assump_637 : (p2 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_53 := assump_10 assump_637
                  apply False.elim assump_53
            case inr assump_36 =>
              cases assump_36
              case intro assump_57 assump_58 =>
                have assump_638 : True := by
                  apply True.intro
                let assump_64 := assump_57 assump_638
                apply False.elim assump_64
        case inr assump_11 =>
          cases assump_3
          case inl assump_70 =>
            cases assump_70
            case inl assump_72 =>
              have assump_639 : (p2 → p2) := by
                intro assump_78
                exact assump_78
              let assump_77 := assump_11 assump_639
              apply False.elim assump_77
            case inr assump_73 =>
              cases assump_73
              case intro assump_84 assump_85 =>
                have assump_640 : True := by
                  apply True.intro
                let assump_90 := assump_85 assump_640
                apply False.elim assump_90
          case inr assump_71 =>
            cases assump_71
            case inl assump_94 =>
              cases assump_94
              case inl assump_96 =>
                have assump_641 : (p2 → p2) := by
                  intro assump_102
                  exact assump_102
                let assump_101 := assump_11 assump_641
                apply False.elim assump_101
              case inr assump_97 =>
                cases assump_97
                case inl assump_108 =>
                  apply False.elim assump_108
                case inr assump_109 =>
                  have assump_642 : (p2 → p2) := by
                    intro assump_116
                    exact assump_116
                  let assump_115 := assump_11 assump_642
                  apply False.elim assump_115
            case inr assump_95 =>
              cases assump_95
              case intro assump_122 assump_123 =>
                have assump_643 : True := by
                  apply True.intro
                let assump_129 := assump_122 assump_643
                apply False.elim assump_129
      case inr assump_7 =>
        cases assump_7
        case inl assump_133 =>
          cases assump_133
          case inl assump_135 =>
            cases assump_5
            case inl assump_139 =>
              cases assump_3
              case inl assump_143 =>
                cases assump_143
                case inl assump_145 =>
                  have assump_644 : (p2 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_150 := assump_139 assump_644
                  apply False.elim assump_150
                case inr assump_146 =>
                  cases assump_146
                  case intro assump_154 assump_155 =>
                    have assump_645 : True := by
                      apply True.intro
                    let assump_160 := assump_155 assump_645
                    apply False.elim assump_160
              case inr assump_144 =>
                cases assump_144
                case inl assump_164 =>
                  cases assump_164
                  case inl assump_166 =>
                    have assump_646 : p5 := by
                      exact assump_135
                    let assump_170 := assump_166 assump_646
                    apply False.elim assump_170
                  case inr assump_167 =>
                    cases assump_167
                    case inl assump_174 =>
                      apply False.elim assump_174
                    case inr assump_175 =>
                      have assump_647 : (p2 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_181 := assump_139 assump_647
                      apply False.elim assump_181
                case inr assump_165 =>
                  cases assump_165
                  case intro assump_185 assump_186 =>
                    have assump_648 : True := by
                      apply True.intro
                    let assump_192 := assump_185 assump_648
                    apply False.elim assump_192
            case inr assump_140 =>
              cases assump_3
              case inl assump_198 =>
                cases assump_198
                case inl assump_200 =>
                  have assump_649 : (p2 → p2) := by
                    intro assump_206
                    exact assump_206
                  let assump_205 := assump_140 assump_649
                  apply False.elim assump_205
                case inr assump_201 =>
                  cases assump_201
                  case intro assump_212 assump_213 =>
                    have assump_650 : True := by
                      apply True.intro
                    let assump_218 := assump_213 assump_650
                    apply False.elim assump_218
              case inr assump_199 =>
                cases assump_199
                case inl assump_222 =>
                  cases assump_222
                  case inl assump_224 =>
                    have assump_651 : p5 := by
                      exact assump_135
                    let assump_228 := assump_224 assump_651
                    apply False.elim assump_228
                  case inr assump_225 =>
                    cases assump_225
                    case inl assump_232 =>
                      apply False.elim assump_232
                    case inr assump_233 =>
                      have assump_652 : (p2 → p2) := by
                        intro assump_240
                        exact assump_240
                      let assump_239 := assump_140 assump_652
                      apply False.elim assump_239
                case inr assump_223 =>
                  cases assump_223
                  case intro assump_246 assump_247 =>
                    have assump_653 : True := by
                      apply True.intro
                    let assump_253 := assump_246 assump_653
                    apply False.elim assump_253
          case inr assump_136 =>
            cases assump_5
            case inl assump_259 =>
              cases assump_3
              case inl assump_263 =>
                cases assump_263
                case inl assump_265 =>
                  have assump_654 : (p2 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_270 := assump_259 assump_654
                  apply False.elim assump_270
                case inr assump_266 =>
                  cases assump_266
                  case intro assump_274 assump_275 =>
                    have assump_655 : True := by
                      apply True.intro
                    let assump_280 := assump_275 assump_655
                    apply False.elim assump_280
              case inr assump_264 =>
                cases assump_264
                case inl assump_284 =>
                  cases assump_284
                  case inl assump_286 =>
                    have assump_656 : (p2 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_291 := assump_259 assump_656
                    apply False.elim assump_291
                  case inr assump_287 =>
                    cases assump_287
                    case inl assump_295 =>
                      apply False.elim assump_295
                    case inr assump_296 =>
                      have assump_657 : (p2 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_302 := assump_259 assump_657
                      apply False.elim assump_302
                case inr assump_285 =>
                  cases assump_285
                  case intro assump_306 assump_307 =>
                    have assump_658 : True := by
                      apply True.intro
                    let assump_313 := assump_306 assump_658
                    apply False.elim assump_313
            case inr assump_260 =>
              cases assump_3
              case inl assump_319 =>
                cases assump_319
                case inl assump_321 =>
                  have assump_659 : (p2 → p2) := by
                    intro assump_327
                    exact assump_327
                  let assump_326 := assump_260 assump_659
                  apply False.elim assump_326
                case inr assump_322 =>
                  cases assump_322
                  case intro assump_333 assump_334 =>
                    have assump_660 : True := by
                      apply True.intro
                    let assump_339 := assump_334 assump_660
                    apply False.elim assump_339
              case inr assump_320 =>
                cases assump_320
                case inl assump_343 =>
                  cases assump_343
                  case inl assump_345 =>
                    have assump_661 : (p2 → p2) := by
                      intro assump_351
                      exact assump_351
                    let assump_350 := assump_260 assump_661
                    apply False.elim assump_350
                  case inr assump_346 =>
                    cases assump_346
                    case inl assump_357 =>
                      apply False.elim assump_357
                    case inr assump_358 =>
                      have assump_662 : (p2 → p2) := by
                        intro assump_365
                        exact assump_365
                      let assump_364 := assump_260 assump_662
                      apply False.elim assump_364
                case inr assump_344 =>
                  cases assump_344
                  case intro assump_371 assump_372 =>
                    have assump_663 : True := by
                      apply True.intro
                    let assump_378 := assump_371 assump_663
                    apply False.elim assump_378
        case inr assump_134 =>
          cases assump_134
          case inl assump_382 =>
            cases assump_5
            case inl assump_386 =>
              cases assump_3
              case inl assump_390 =>
                cases assump_390
                case inl assump_392 =>
                  have assump_664 : (p2 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_397 := assump_386 assump_664
                  apply False.elim assump_397
                case inr assump_393 =>
                  cases assump_393
                  case intro assump_401 assump_402 =>
                    have assump_665 : True := by
                      apply True.intro
                    let assump_407 := assump_402 assump_665
                    apply False.elim assump_407
              case inr assump_391 =>
                cases assump_391
                case inl assump_411 =>
                  cases assump_411
                  case inl assump_413 =>
                    have assump_666 : (p2 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_418 := assump_386 assump_666
                    apply False.elim assump_418
                  case inr assump_414 =>
                    cases assump_414
                    case inl assump_422 =>
                      apply False.elim assump_422
                    case inr assump_423 =>
                      have assump_667 : (p2 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_429 := assump_386 assump_667
                      apply False.elim assump_429
                case inr assump_412 =>
                  cases assump_412
                  case intro assump_433 assump_434 =>
                    have assump_668 : True := by
                      apply True.intro
                    let assump_440 := assump_433 assump_668
                    apply False.elim assump_440
            case inr assump_387 =>
              cases assump_3
              case inl assump_446 =>
                cases assump_446
                case inl assump_448 =>
                  have assump_669 : (p2 → p2) := by
                    intro assump_454
                    exact assump_454
                  let assump_453 := assump_387 assump_669
                  apply False.elim assump_453
                case inr assump_449 =>
                  cases assump_449
                  case intro assump_460 assump_461 =>
                    have assump_670 : True := by
                      apply True.intro
                    let assump_466 := assump_461 assump_670
                    apply False.elim assump_466
              case inr assump_447 =>
                cases assump_447
                case inl assump_470 =>
                  cases assump_470
                  case inl assump_472 =>
                    have assump_671 : (p2 → p2) := by
                      intro assump_478
                      exact assump_478
                    let assump_477 := assump_387 assump_671
                    apply False.elim assump_477
                  case inr assump_473 =>
                    cases assump_473
                    case inl assump_484 =>
                      apply False.elim assump_484
                    case inr assump_485 =>
                      have assump_672 : (p2 → p2) := by
                        intro assump_492
                        exact assump_492
                      let assump_491 := assump_387 assump_672
                      apply False.elim assump_491
                case inr assump_471 =>
                  cases assump_471
                  case intro assump_498 assump_499 =>
                    have assump_673 : True := by
                      apply True.intro
                    let assump_505 := assump_498 assump_673
                    apply False.elim assump_505
          case inr assump_383 =>
            cases assump_5
            case inl assump_511 =>
              cases assump_3
              case inl assump_515 =>
                cases assump_515
                case inl assump_517 =>
                  have assump_674 : (p2 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_522 := assump_511 assump_674
                  apply False.elim assump_522
                case inr assump_518 =>
                  cases assump_518
                  case intro assump_526 assump_527 =>
                    have assump_675 : True := by
                      apply True.intro
                    let assump_532 := assump_527 assump_675
                    apply False.elim assump_532
              case inr assump_516 =>
                cases assump_516
                case inl assump_536 =>
                  cases assump_536
                  case inl assump_538 =>
                    have assump_676 : (p2 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_543 := assump_511 assump_676
                    apply False.elim assump_543
                  case inr assump_539 =>
                    cases assump_539
                    case inl assump_547 =>
                      apply False.elim assump_547
                    case inr assump_548 =>
                      have assump_677 : (p2 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_554 := assump_511 assump_677
                      apply False.elim assump_554
                case inr assump_537 =>
                  cases assump_537
                  case intro assump_558 assump_559 =>
                    have assump_678 : True := by
                      apply True.intro
                    let assump_565 := assump_558 assump_678
                    apply False.elim assump_565
            case inr assump_512 =>
              cases assump_3
              case inl assump_571 =>
                cases assump_571
                case inl assump_573 =>
                  have assump_679 : (p2 → p2) := by
                    intro assump_579
                    exact assump_579
                  let assump_578 := assump_512 assump_679
                  apply False.elim assump_578
                case inr assump_574 =>
                  cases assump_574
                  case intro assump_585 assump_586 =>
                    have assump_680 : True := by
                      apply True.intro
                    let assump_591 := assump_586 assump_680
                    apply False.elim assump_591
              case inr assump_572 =>
                cases assump_572
                case inl assump_595 =>
                  cases assump_595
                  case inl assump_597 =>
                    have assump_681 : (p2 → p2) := by
                      intro assump_603
                      exact assump_603
                    let assump_602 := assump_512 assump_681
                    apply False.elim assump_602
                  case inr assump_598 =>
                    cases assump_598
                    case inl assump_609 =>
                      apply False.elim assump_609
                    case inr assump_610 =>
                      have assump_682 : (p2 → p2) := by
                        intro assump_617
                        exact assump_617
                      let assump_616 := assump_512 assump_682
                      apply False.elim assump_616
                case inr assump_596 =>
                  cases assump_596
                  case intro assump_623 assump_624 =>
                    have assump_683 : True := by
                      apply True.intro
                    let assump_630 := assump_623 assump_683
                    apply False.elim assump_630


variable (p6 p2 p5 p1 : Prop)
theorem file27_27549 : (((((False ∧ False) ∨ (False ∧ False)) ∧ ((False → False) ∧ (False ∧ p5))) ∧ (((p6 ∧ p1) → False) ∧ ((p5 → p2) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8
      case inr assump_7 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p7 p0 p6 p1 p4 p3 : Prop)
theorem file27_28145 : (((((p1 → False) → False) → ((p6 → p7) → False)) ∨ (((p3 ∨ p1) ∧ (p1 → False)) → False)) → ((((True → False) → False) ∨ ((p3 ∧ p4) → (p6 ∧ False))) ∨ (((False ∧ p0) → (False ∧ p3)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    have assump_22 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_22
    apply False.elim assump_9
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_15
    have assump_23 : True := by
      apply True.intro
    let assump_18 := assump_15 assump_23
    apply False.elim assump_18


variable (p5 p2 p3 p4 p7 p1 p6 p0 : Prop)
theorem file27_28847 : ((((((p3 → p4) ∧ (p0 ∧ p5)) → False) ∧ (((p7 → p5) ∧ (False ∧ False)) ∧ ((p3 → False) → (p3 → False)))) ∧ ((((p2 → p4) → (p3 ∧ p2)) ∧ ((False → False) ∧ (p5 → p3))) ∧ (((p6 ∧ p7) ∨ (p1 → p7)) → ((p3 ∧ p2) ∨ (True ∧ False))))) → False) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            apply False.elim assump_21


variable (p3 p2 p0 p1 p7 p6 p4 : Prop)
theorem file27_29514 : (((((True → True) ∧ (p1 ∧ p4)) → False) ∧ (((p4 ∧ p6) ∧ (p7 ∨ p1)) ∧ ((p1 ∨ p7) → False))) → ((((True ∨ False) ∨ (p0 ∧ p7)) → False) ∧ (((p0 ∨ p2) ∨ (p0 ∨ p7)) ∧ ((p7 ∧ True) ∧ (p3 ∨ p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              cases assump_16
              case inl assump_23 =>
                have assump_161 : (p1 ∨ p7) := by
                  apply Or.inr
                  exact assump_23
                let assump_29 := assump_14 assump_161
                apply False.elim assump_29
              case inr assump_24 =>
                have assump_162 : (p1 ∨ p7) := by
                  apply Or.inl
                  exact assump_24
                let assump_37 := assump_14 assump_162
                apply False.elim assump_37
    case inr assump_6 =>
      apply False.elim assump_6
  case inr assump_4 =>
    cases assump_4
    case intro assump_43 assump_44 =>
      cases assump_1
      case intro assump_49 assump_50 =>
        cases assump_50
        case intro assump_53 assump_54 =>
          cases assump_53
          case intro assump_55 assump_56 =>
            cases assump_55
            case intro assump_57 assump_58 =>
              cases assump_56
              case inl assump_63 =>
                have assump_163 : (p1 ∨ p7) := by
                  apply Or.inr
                  exact assump_63
                let assump_69 := assump_54 assump_163
                apply False.elim assump_69
              case inr assump_64 =>
                have assump_164 : (p1 ∨ p7) := by
                  apply Or.inl
                  exact assump_64
                let assump_77 := assump_54 assump_164
                apply False.elim assump_77
  apply And.intro
  cases assump_1
  case intro assump_81 assump_82 =>
    cases assump_82
    case intro assump_85 assump_86 =>
      cases assump_85
      case intro assump_87 assump_88 =>
        cases assump_87
        case intro assump_89 assump_90 =>
          cases assump_88
          case inl assump_95 =>
            apply Or.inr
            apply Or.inr
            exact assump_95
          case inr assump_96 =>
            have assump_165 : (p1 ∨ p7) := by
              apply Or.inl
              exact assump_96
            let assump_105 := assump_86 assump_165
            apply False.elim assump_105
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_109 assump_110 =>
    cases assump_110
    case intro assump_113 assump_114 =>
      cases assump_113
      case intro assump_115 assump_116 =>
        cases assump_115
        case intro assump_117 assump_118 =>
          cases assump_116
          case inl assump_123 =>
            exact assump_123
          case inr assump_124 =>
            have assump_166 : (p1 ∨ p7) := by
              apply Or.inl
              exact assump_124
            let assump_133 := assump_114 assump_166
            apply False.elim assump_133
  apply True.intro
  cases assump_1
  case intro assump_137 assump_138 =>
    cases assump_138
    case intro assump_141 assump_142 =>
      cases assump_141
      case intro assump_143 assump_144 =>
        cases assump_143
        case intro assump_145 assump_146 =>
          cases assump_144
          case inl assump_151 =>
            apply Or.inr
            exact assump_145
          case inr assump_152 =>
            apply Or.inr
            exact assump_145


variable (p6 p5 p1 p3 p2 p4 : Prop)
theorem file27_33330 : (((((p4 → False) → (p1 ∨ p6)) ∧ ((p2 → False) ∧ (p1 ∧ p2))) → False) ∨ ((((p1 ∧ p3) ∧ (p1 ∨ True)) → ((p5 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_22 : p2 := by
          exact assump_11
        let assump_18 := assump_6 assump_22
        apply False.elim assump_18


variable (p2 p6 p5 p7 : Prop)
theorem file27_33863 : ((((((p5 ∨ p2) ∨ (False ∧ p6)) ∨ ((p2 → False) ∨ (p7 → False))) ∨ (((p2 → False) ∧ (p7 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p5 ∨ p2) ∨ (False ∧ p6)) ∨ ((p2 → False) ∨ (p7 → False))) ∨ (((p2 → False) ∧ (p7 ∧ False)) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_5
    have assump_17 : ((((p5 ∨ p2) ∨ (False ∧ p6)) ∨ ((p2 → False) ∨ (p7 → False))) ∨ (((p2 → False) ∧ (p7 ∧ False)) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p6 p3 p4 p1 p5 p7 : Prop)
theorem file27_34637 : (((((p6 → True) ∧ (p5 → False)) ∧ ((False ∨ p4) → (p5 → False))) ∨ (((True → p2) → False) ∨ ((False → False) ∧ (p6 → p1)))) → ((((p1 ∨ p4) → (p5 → p4)) → ((False ∧ p2) ∧ (p6 → False))) → (((p3 ∨ p2) ∧ (p7 ∧ False)) → ((False → p3) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_8
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    case inr assump_10 =>
      cases assump_8
      case intro assump_21 assump_22 =>
        apply False.elim assump_22


variable (p0 p3 p6 p5 : Prop)
theorem file27_35321 : ((((((p3 ∨ p6) ∧ (p5 → False)) → ((False ∨ p0) ∨ (False ∧ True))) → False) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → False) → False) → False) := by
      intro assump_9
      have assump_23 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p0 p5 p7 p2 p1 p3 p6 p4 : Prop)
theorem file27_35926 : (((((p3 → p1) ∧ (p5 → p4)) → ((p3 ∧ p0) ∨ (p1 → False))) ∧ (((False ∨ True) ∧ (p1 → p4)) → False)) → ((((p6 → p7) ∨ (p1 → False)) ∧ ((p4 ∧ p0) ∧ (p2 → False))) → (((p3 ∧ p4) → (p0 → p0)) ∨ ((p3 ∨ p7) ∨ (p5 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_1
          case intro assump_19 assump_20 =>
            apply Or.inl
            intro assump_25
            intro assump_26
            cases assump_25
            case intro assump_29 assump_30 =>
              exact assump_26
    case inr assump_6 =>
      cases assump_4
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          cases assump_1
          case intro assump_47 assump_48 =>
            apply Or.inl
            intro assump_53
            intro assump_54
            cases assump_53
            case intro assump_57 assump_58 =>
              exact assump_54


variable (p4 p1 p6 p5 p2 p0 : Prop)
theorem file27_37122 : (((((p1 ∨ p1) → False) → ((p1 ∧ p2) → False)) → False) → ((((p6 → p1) ∧ (True → False)) → False) ∧ (((p5 ∨ p4) → False) ∨ ((True → p5) → (p0 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_76 : (((p1 ∨ p1) → False) → ((p1 ∧ p2) → False)) := by
      intro assump_12
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        have assump_77 : (p1 ∨ p1) := by
          apply Or.inl
          exact assump_14
        let assump_22 := assump_12 assump_77
        apply False.elim assump_22
    let assump_11 := assump_1 assump_76
    apply False.elim assump_11
  apply Or.inl
  intro assump_31
  cases assump_31
  case inl assump_32 =>
    have assump_78 : (((p1 ∨ p1) → False) → ((p1 ∧ p2) → False)) := by
      intro assump_38
      intro assump_39
      cases assump_39
      case intro assump_40 assump_41 =>
        have assump_79 : (p1 ∨ p1) := by
          apply Or.inl
          exact assump_40
        let assump_48 := assump_38 assump_79
        apply False.elim assump_48
    let assump_37 := assump_1 assump_78
    apply False.elim assump_37
  case inr assump_33 =>
    have assump_80 : (((p1 ∨ p1) → False) → ((p1 ∧ p2) → False)) := by
      intro assump_59
      intro assump_60
      cases assump_60
      case intro assump_61 assump_62 =>
        have assump_81 : (p1 ∨ p1) := by
          apply Or.inl
          exact assump_61
        let assump_69 := assump_59 assump_81
        apply False.elim assump_69
    let assump_58 := assump_1 assump_80
    apply False.elim assump_58


variable (p5 p1 p3 : Prop)
theorem file27_38789 : ((((((True → False) → False) ∨ ((p1 → False) → (p5 ∧ p1))) ∨ (((p3 ∨ p5) ∧ (False → False)) → False)) → False) → False) := by
  intro assump_30
  have assump_44 : ((((True → False) → False) ∨ ((p1 → False) → (p5 ∧ p1))) ∨ (((p3 ∨ p5) ∧ (False → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_34
    have assump_45 : True := by
      apply True.intro
    let assump_37 := assump_34 assump_45
    apply False.elim assump_37
  let assump_33 := assump_30 assump_44
  apply False.elim assump_33


variable (p6 p4 p7 p5 p2 p1 p3 : Prop)
theorem file27_39370 : (((((True ∧ p3) ∨ (p1 → p3)) ∧ ((p4 ∨ p3) → False)) → (((p2 ∧ p1) ∨ (True ∨ False)) ∨ ((p6 → False) ∨ (p5 → p1)))) ∨ ((((p6 ∧ True) → False) → ((p3 → False) → (p1 ∨ p4))) ∧ (((p4 ∧ p4) → False) ∧ ((p3 ∧ p7) → (True ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply True.intro


variable (p0 p7 p6 p3 p4 p2 p5 : Prop)
theorem file27_40043 : (((((False ∧ False) ∧ (True ∧ p3)) → ((False ∨ p0) ∨ (p6 → p3))) ∨ (((p5 → False) ∨ (True ∨ p6)) ∨ ((False → False) → False))) ∨ ((((p2 → True) → False) ∧ ((p3 ∨ p6) ∧ (p5 → False))) ∧ (((p7 → False) ∨ (p7 ∨ p4)) → ((p0 → False) ∧ (p0 → p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      apply False.elim assump_16


variable (p4 p3 p6 p5 p1 p2 : Prop)
theorem file27_40547 : (((((p2 ∧ p3) → False) → False) ∧ (((True → False) ∨ (p3 → False)) ∧ ((False ∨ p2) ∧ (p1 → False)))) → ((((False → p1) ∧ (p1 ∨ False)) → ((p3 → p5) → (p4 ∨ p6))) ∧ (((True ∨ False) ∧ (True ∧ True)) ∨ ((True → False) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_19
            case intro assump_24 assump_25 =>
              cases assump_24
              case inl assump_26 =>
                apply False.elim assump_26
              case inr assump_27 =>
                have assump_88 : p1 := by
                  exact assump_10
                let assump_34 := assump_25 assump_88
                apply False.elim assump_34
          case inr assump_21 =>
            cases assump_19
            case intro assump_40 assump_41 =>
              cases assump_40
              case inl assump_42 =>
                apply False.elim assump_42
              case inr assump_43 =>
                have assump_89 : p1 := by
                  exact assump_10
                let assump_50 := assump_41 assump_89
                apply False.elim assump_50
    case inr assump_11 =>
      apply False.elim assump_11
  cases assump_1
  case intro assump_56 assump_57 =>
    cases assump_57
    case intro assump_60 assump_61 =>
      cases assump_60
      case inl assump_62 =>
        cases assump_61
        case intro assump_66 assump_67 =>
          cases assump_66
          case inl assump_68 =>
            apply False.elim assump_68
          case inr assump_69 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            apply True.intro
            apply And.intro
            apply True.intro
            apply True.intro
      case inr assump_63 =>
        cases assump_61
        case intro assump_78 assump_79 =>
          cases assump_78
          case inl assump_80 =>
            apply False.elim assump_80
          case inr assump_81 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            apply True.intro
            apply And.intro
            apply True.intro
            apply True.intro


variable (p3 p1 p7 p6 p2 : Prop)
theorem file27_43026 : ((((((False → False) → (p6 → False)) ∧ ((False ∧ False) ∨ (p3 ∧ p6))) → (((p1 ∧ p3) → False) ∨ ((p2 → False) → (p7 → True)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((False → False) → (p6 → False)) ∧ ((False ∧ False) ∨ (p3 ∧ p6))) → (((p1 ∧ p3) → False) ∨ ((p2 → False) → (p7 → True)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_11 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          apply Or.inl
          intro assump_22
          cases assump_22
          case intro assump_23 assump_24 =>
            have assump_45 : (False → False) := by
              intro assump_34
              apply False.elim assump_34
            let assump_33 := assump_6 assump_45
            have assump_46 : p6 := by
              exact assump_17
            let assump_37 := assump_33 assump_46
            apply False.elim assump_37
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p3 p7 p0 p6 p1 p2 : Prop)
theorem file27_44232 : (((((p0 ∧ p0) ∨ (p1 ∨ True)) → False) → (((p1 → False) ∨ (p2 → False)) ∨ ((p2 → False) ∨ (p7 ∧ p6)))) ∨ ((((False → p0) ∨ (p0 → False)) → ((False → False) → False)) ∨ (((p0 ∧ True) → (p6 → False)) → ((p3 → False) → (p0 → p1))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_12 : ((p0 ∧ p0) ∨ (p1 ∨ True)) := by
    apply Or.inr
    apply Or.inl
    exact assump_4
  let assump_8 := assump_1 assump_12
  apply False.elim assump_8


variable (p0 p6 p2 p4 p3 p5 p7 : Prop)
theorem file27_44778 : (((((p5 ∨ True) → (p4 → p5)) ∧ ((False ∨ p6) ∧ (p4 → p3))) ∧ (((p7 → p7) ∧ (p2 ∧ p0)) ∧ ((False ∧ p0) ∧ (p2 ∨ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_19
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case intro assump_32 assump_33 =>
                    apply False.elim assump_32


variable (p0 p7 p6 p1 p5 p4 p2 : Prop)
theorem file27_45711 : (((((p7 ∨ p0) → (p1 ∨ False)) ∧ ((p5 → p7) ∧ (p2 ∧ True))) ∧ (((p2 ∨ True) → False) ∧ ((p7 ∨ p0) → False))) → ((((p1 → False) ∨ (True ∨ p6)) → False) ∧ (((False ∨ False) → (p4 → False)) ∨ ((p4 ∧ p0) ∧ (p7 ∧ p1))))) := by
  intro assump_22
  apply And.intro
  intro assump_23
  cases assump_23
  case inl assump_24 =>
    cases assump_22
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        cases assump_31
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            cases assump_29
            case intro assump_44 assump_45 =>
              have assump_147 : (p2 ∨ True) := by
                apply Or.inl
                exact assump_38
              let assump_51 := assump_44 assump_147
              apply False.elim assump_51
  case inr assump_25 =>
    cases assump_25
    case inl assump_55 =>
      cases assump_22
      case intro assump_59 assump_60 =>
        cases assump_59
        case intro assump_61 assump_62 =>
          cases assump_62
          case intro assump_65 assump_66 =>
            cases assump_66
            case intro assump_69 assump_70 =>
              cases assump_60
              case intro assump_75 assump_76 =>
                have assump_148 : (p2 ∨ True) := by
                  apply Or.inl
                  exact assump_69
                let assump_82 := assump_75 assump_148
                apply False.elim assump_82
    case inr assump_56 =>
      cases assump_22
      case intro assump_88 assump_89 =>
        cases assump_88
        case intro assump_90 assump_91 =>
          cases assump_91
          case intro assump_94 assump_95 =>
            cases assump_95
            case intro assump_98 assump_99 =>
              cases assump_89
              case intro assump_104 assump_105 =>
                have assump_149 : (p2 ∨ True) := by
                  apply Or.inl
                  exact assump_98
                let assump_111 := assump_104 assump_149
                apply False.elim assump_111
  cases assump_22
  case intro assump_115 assump_116 =>
    cases assump_115
    case intro assump_117 assump_118 =>
      cases assump_118
      case intro assump_121 assump_122 =>
        cases assump_122
        case intro assump_125 assump_126 =>
          cases assump_116
          case intro assump_131 assump_132 =>
            apply Or.inl
            intro assump_137
            intro assump_138
            cases assump_137
            case inl assump_141 =>
              apply False.elim assump_141
            case inr assump_142 =>
              apply False.elim assump_142


variable (p7 p1 p3 p4 p5 : Prop)
theorem file27_48438 : (((((False → False) → (p1 → False)) → False) ∧ (((True → p3) ∧ (p3 ∧ p1)) → False)) → ((((False ∨ p7) → (p3 → False)) ∧ ((False ∧ False) → (p7 ∧ p1))) ∨ (((p3 → p4) ∧ (True ∨ p5)) ∨ ((p5 ∧ p5) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_8
    intro assump_9
    cases assump_8
    case inl assump_12 =>
      apply False.elim assump_12
    case inr assump_13 =>
      have assump_54 : ((False → False) → (p1 → False)) := by
        intro assump_25
        intro assump_26
        have assump_55 : ((True → p3) ∧ (p3 ∧ p1)) := by
          apply And.intro
          intro assump_36
          exact assump_9
          apply And.intro
          exact assump_9
          exact assump_26
        let assump_35 := assump_3 assump_55
        apply False.elim assump_35
      let assump_24 := assump_2 assump_54
      apply False.elim assump_24
    intro assump_45
    apply And.intro
    cases assump_45
    case intro assump_46 assump_47 =>
      apply False.elim assump_46
    cases assump_45
    case intro assump_50 assump_51 =>
      apply False.elim assump_50


variable (p4 p5 p6 : Prop)
theorem file27_49644 : ((((((False → p6) → (False ∧ p5)) → False) ∧ (((p5 → False) ∧ (p4 ∧ False)) → False)) → False) → False) := by
  intro assump_5
  have assump_34 : ((((False → p6) → (False ∧ p5)) → False) ∧ (((p5 → False) ∧ (p4 ∧ False)) → False)) := by
    apply And.intro
    intro assump_9
    have assump_35 : (False → p6) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_9 assump_35
    let assump_16 := And.left assump_12
    apply False.elim assump_16
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      cases assump_22
      case intro assump_25 assump_26 =>
        apply False.elim assump_26
  let assump_8 := assump_5 assump_34
  apply False.elim assump_8


variable (p6 p3 p4 p7 p1 p5 : Prop)
theorem file27_50425 : (((((False ∧ p7) ∧ (p1 ∨ p5)) ∧ ((True → True) ∧ (p3 → p5))) ∧ (((p4 → False) → (p1 ∨ p5)) ∨ ((p6 → p4) → (p3 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8


variable (p7 p2 p0 p6 p3 p5 : Prop)
theorem file27_50903 : ((((((p7 → False) ∧ (p5 → p2)) ∨ ((p3 → False) → False)) → (((p5 ∧ False) → False) ∨ ((p6 → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p7 → False) ∧ (p5 → p2)) ∨ ((p3 → False) → False)) → (((p5 ∧ False) → False) ∨ ((p6 → p0) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
    case inr assump_7 =>
      apply Or.inl
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        apply False.elim assump_25
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p6 p2 p3 p5 p4 p1 p0 : Prop)
theorem file27_51742 : (((((p4 ∧ p3) → (p0 ∧ p1)) ∧ ((True → False) ∧ (p1 ∨ p6))) → False) ∧ ((((p5 → False) ∧ (p5 ∧ p4)) ∨ ((p5 → False) ∧ (p2 ∧ p2))) → (((p5 → False) → False) → False))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_75 : True := by
          apply True.intro
        let assump_15 := assump_6 assump_75
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_76 : True := by
          apply True.intro
        let assump_22 := assump_6 assump_76
        apply False.elim assump_22
  intro assump_26
  intro assump_27
  cases assump_26
  case inl assump_30 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_33
      case intro assump_36 assump_37 =>
        have assump_77 : p5 := by
          exact assump_36
        let assump_44 := assump_32 assump_77
        apply False.elim assump_44
  case inr assump_31 =>
    cases assump_31
    case intro assump_48 assump_49 =>
      cases assump_49
      case intro assump_52 assump_53 =>
        have assump_78 : (p5 → False) := by
          intro assump_62
          have assump_79 : p5 := by
            exact assump_62
          let assump_68 := assump_48 assump_79
          apply False.elim assump_68
        let assump_61 := assump_27 assump_78
        apply False.elim assump_61


variable (p0 p6 p2 p1 p7 p5 : Prop)
theorem file27_53256 : (((((True ∨ p5) ∨ (p7 → p5)) → False) → (((p0 ∧ p0) ∨ (p2 → False)) → False)) ∨ ((((True ∧ False) ∨ (p6 ∧ p2)) → ((p1 → False) → False)) → (((p2 → p6) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_25 : ((True ∨ p5) ∨ (p7 → p5)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_13 := assump_1 assump_25
      apply False.elim assump_13
  case inr assump_4 =>
    have assump_26 : ((True ∨ p5) ∨ (p7 → p5)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_21 := assump_1 assump_26
    apply False.elim assump_21


variable (p5 p7 p4 p3 p1 p2 : Prop)
theorem file27_54042 : (((((p4 ∨ p1) ∨ (p2 ∧ p5)) → False) → False) → ((((True ∨ p7) → False) → False) ∨ (((p3 ∨ p2) → False) ∧ ((p5 ∨ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : (True ∨ p7) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p7 p4 p5 p3 p1 p2 p0 : Prop)
theorem file27_54428 : (((((p3 ∨ p1) → False) ∧ ((p0 → p2) ∨ (p4 ∧ p5))) ∧ (((False → False) → False) ∧ ((p3 ∧ p5) → (p1 → False)))) → ((((p1 → False) ∧ (p7 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          have assump_49 : (False → False) := by
            intro assump_23
            apply False.elim assump_23
          let assump_22 := assump_15 assump_49
          apply False.elim assump_22
      case inr assump_12 =>
        cases assump_12
        case intro assump_29 assump_30 =>
          cases assump_6
          case intro assump_35 assump_36 =>
            have assump_50 : (False → False) := by
              intro assump_43
              apply False.elim assump_43
            let assump_42 := assump_35 assump_50
            apply False.elim assump_42


variable (p4 p6 p3 p1 p7 : Prop)
theorem file27_55481 : (((((p7 → p1) → False) → ((p6 → False) ∧ (p4 → False))) ∧ (((p3 → p3) → False) ∧ ((p7 ∧ p1) → (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_20 : (p3 → p3) := by
        intro assump_14
        exact assump_14
      let assump_13 := assump_6 assump_20
      apply False.elim assump_13


variable (p3 p4 p0 p1 p6 : Prop)
theorem file27_55948 : (((((p1 ∧ p0) ∧ (False → p0)) → ((False → False) ∨ (p1 → False))) → False) → ((((p3 ∧ p4) ∨ (p6 ∨ p6)) → False) → False)) := by
  intro assump_19
  intro assump_20
  have assump_43 : (((p1 ∧ p0) ∧ (False → p0)) → ((False → False) ∨ (p1 → False))) := by
    intro assump_26
    cases assump_26
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        apply Or.inl
        intro assump_37
        apply False.elim assump_37
  let assump_25 := assump_19 assump_43
  apply False.elim assump_25


variable (p7 p2 p4 p0 p3 : Prop)
theorem file27_56546 : (((((p3 → p7) → False) → False) ∧ (((True → p7) ∧ (p4 → p4)) → False)) → ((((p2 ∧ p7) → False) → ((p2 → False) ∧ (p3 → False))) → (((False → p0) → (p7 → p2)) → ((False → False) ∨ (p2 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    apply Or.inl
    intro assump_14
    apply False.elim assump_14


variable (p6 p2 p4 p0 p7 p5 p3 p1 : Prop)
theorem file27_56981 : (((((p3 ∧ p0) ∧ (p2 ∨ p0)) ∧ ((p4 → p4) ∧ (p4 → p0))) → False) → ((((p7 ∧ p0) → (p6 → False)) → ((p1 → p2) → False)) → (((p3 ∧ p2) → False) ∨ ((p1 → p1) ∨ (p5 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_50 : ((p7 ∧ p0) → (p6 → False)) := by
      intro assump_18
      intro assump_19
      cases assump_18
      case intro assump_22 assump_23 =>
        have assump_51 : (((p3 ∧ p0) ∧ (p2 ∨ p0)) ∧ ((p4 → p4) ∧ (p4 → p0))) := by
          apply And.intro
          apply And.intro
          apply And.intro
          exact assump_8
          exact assump_23
          apply Or.inl
          exact assump_9
          apply And.intro
          intro assump_34
          exact assump_34
          intro assump_37
          exact assump_23
        let assump_33 := assump_1 assump_51
        apply False.elim assump_33
    let assump_17 := assump_2 assump_50
    have assump_52 : (p1 → p2) := by
      intro assump_44
      exact assump_9
    let assump_43 := assump_17 assump_52
    apply False.elim assump_43


variable (p0 p4 p3 p2 : Prop)
theorem file27_58148 : (((((p3 → False) → False) ∨ ((p0 → False) ∧ (p4 ∧ p4))) ∧ (((p2 → False) → False) ∧ ((False → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_40 : (False → True) := by
          intro assump_15
          apply True.intro
        let assump_14 := assump_9 assump_40
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case intro assump_19 assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          cases assump_3
          case intro assump_29 assump_30 =>
            have assump_41 : (False → True) := by
              intro assump_36
              apply True.intro
            let assump_35 := assump_30 assump_41
            apply False.elim assump_35


variable (p0 p5 p7 p1 : Prop)
theorem file27_59097 : (((((False ∧ p0) → (p1 ∧ p1)) → False) → False) → ((((p5 ∧ p7) → False) → ((True → False) → (p5 → False))) ∨ (((p5 ∨ True) ∨ (p7 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  have assump_18 : True := by
    apply True.intro
  let assump_14 := assump_5 assump_18
  apply False.elim assump_14


variable (p1 p2 p6 p3 p7 : Prop)
theorem file27_59511 : ((((((p6 → p6) ∨ (p7 ∨ True)) ∨ ((p3 → False) ∧ (p2 → False))) → False) ∧ ((((p1 ∧ True) ∧ (True ∧ True)) ∧ ((p6 → False) ∧ (p3 ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p6 → p6) ∨ (p7 ∨ True)) ∨ ((p3 → False) ∧ (p2 → False))) := by
      apply Or.inl
      apply Or.inl
      intro assump_10
      exact assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p6 p2 p3 p5 p7 p0 p4 : Prop)
theorem file27_60041 : (((((p0 ∨ True) → False) → False) ∨ (((p7 → p3) → (p4 ∨ p4)) ∨ ((p4 ∨ p4) ∧ (p0 → p7)))) ∨ ((((p5 ∨ p2) → False) → ((p6 → False) ∨ (False → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (p0 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p2 p5 p3 p1 p4 : Prop)
theorem file27_60451 : ((((((p1 ∧ p4) → (p7 → False)) → False) → False) ∧ ((((p5 ∧ p2) ∧ (p7 → p2)) ∨ ((p7 ∧ p7) ∧ (p3 → p1))) ∧ (((p4 ∧ p3) ∨ (p7 ∨ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_42 : ((p4 ∧ p3) ∨ (p7 ∨ p5)) := by
              apply Or.inr
              apply Or.inr
              exact assump_12
            let assump_22 := assump_7 assump_42
            apply False.elim assump_22
      case inr assump_9 =>
        cases assump_9
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            have assump_43 : ((p4 ∧ p3) ∨ (p7 ∨ p5)) := by
              apply Or.inr
              apply Or.inl
              exact assump_29
            let assump_38 := assump_7 assump_43
            apply False.elim assump_38


variable (p7 p2 p0 p5 p3 p6 p1 : Prop)
theorem file27_61599 : (((((p7 ∧ True) ∧ (p2 ∨ p0)) ∧ ((p5 ∨ p2) ∨ (p1 ∨ False))) → (((p6 ∨ p7) ∧ (False ∧ p7)) → False)) ∨ ((((p2 ∧ p5) ∨ (True ∨ False)) ∨ ((True ∨ p1) → False)) ∨ (((True → False) → (p1 → p3)) ∨ ((p1 ∧ p0) → (p5 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_6 =>
      cases assump_4
      case intro assump_15 assump_16 =>
        apply False.elim assump_15


variable (p5 p7 p0 : Prop)
theorem file27_62236 : (((((False ∨ True) ∨ (p5 ∨ p0)) ∨ ((False → False) → (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((False ∨ True) ∨ (p5 ∨ p0)) ∨ ((False → False) → (p7 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p3 p6 p0 p2 p1 p4 p5 : Prop)
theorem file27_62637 : (((((p4 ∧ True) ∨ (p7 ∨ True)) → ((p1 ∨ p5) ∨ (False → False))) ∨ (((p6 ∧ p1) → (p6 → p5)) → ((False → p1) ∨ (False → False)))) ∨ ((((p3 → p2) → False) ∨ ((p2 ∧ p2) ∨ (p4 → False))) → (((p4 → p3) → False) → ((p0 → p4) ∨ (p1 ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inr
      intro assump_10
      apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case inl assump_13 =>
      apply Or.inr
      intro assump_17
      apply False.elim assump_17
    case inr assump_14 =>
      apply Or.inr
      intro assump_22
      apply False.elim assump_22


variable (p0 p3 p2 p7 p6 p5 p4 : Prop)
theorem file27_63398 : (((((p3 ∧ False) → (p5 ∨ True)) → False) ∨ (((p6 → p4) ∨ (p3 → p5)) ∨ ((p7 ∨ p2) → False))) → ((((p0 ∧ False) → (p0 → p6)) ∨ ((p7 → False) ∨ (True → False))) ∨ (((False → p7) → (p4 → p6)) → ((p2 → False) ∧ (p2 ∨ p6))))) := by
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    apply Or.inl
    apply Or.inl
    intro assump_14
    intro assump_15
    cases assump_14
    case intro assump_18 assump_19 =>
      apply False.elim assump_19
  case inr assump_11 =>
    cases assump_11
    case inl assump_24 =>
      cases assump_24
      case inl assump_26 =>
        apply Or.inl
        apply Or.inl
        intro assump_30
        intro assump_31
        cases assump_30
        case intro assump_34 assump_35 =>
          apply False.elim assump_35
      case inr assump_27 =>
        apply Or.inl
        apply Or.inl
        intro assump_42
        intro assump_43
        cases assump_42
        case intro assump_46 assump_47 =>
          apply False.elim assump_47
    case inr assump_25 =>
      apply Or.inl
      apply Or.inl
      intro assump_54
      intro assump_55
      cases assump_54
      case intro assump_58 assump_59 =>
        apply False.elim assump_59


variable (p6 p3 p1 p7 p0 p2 p5 p4 : Prop)
theorem file27_64652 : (((((p0 ∨ p5) ∨ (False → p5)) → ((p0 ∨ p1) → False)) → (((p1 → True) ∧ (p4 → p3)) ∧ ((p2 ∧ p0) ∨ (p4 ∧ p2)))) → ((((p0 → p7) ∨ (p7 → False)) → ((True ∧ False) → False)) ∨ (((True ∧ p4) ∧ (p2 ∨ p0)) ∧ ((p4 ∧ p4) → (p0 ∧ p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p6 p2 p0 : Prop)
theorem file27_65083 : (((((True → False) → (True → False)) → False) ∧ (((False → False) → False) ∨ ((p0 → False) ∧ (p6 → p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_39 : (False → False) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_6 assump_39
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_17 assump_18 =>
        have assump_40 : ((True → False) → (True → False)) := by
          intro assump_26
          intro assump_27
          have assump_41 : True := by
            apply True.intro
          let assump_32 := assump_26 assump_41
          apply False.elim assump_32
        let assump_25 := assump_2 assump_40
        apply False.elim assump_25


variable (p3 : Prop)
theorem file27_65973 : ((((((False → False) ∧ (p3 ∨ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) ∧ (p3 ∨ True)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → False) ∧ (p3 ∨ True)) := by
      apply And.intro
      intro assump_9
      apply False.elim assump_9
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p3 p0 p6 : Prop)
theorem file27_66528 : (((((p1 ∨ p1) → False) ∧ ((p0 → p0) ∧ (p6 → False))) ∧ (((p1 ∧ p3) → (p3 → p3)) ∧ ((p3 → p3) → False))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        cases assump_13
        case intro assump_24 assump_25 =>
          have assump_37 : (p3 → p3) := by
            intro assump_31
            exact assump_31
          let assump_30 := assump_25 assump_37
          apply False.elim assump_30


variable (p2 p0 p5 p6 p3 p1 p4 p7 : Prop)
theorem file27_67154 : (((((p4 ∧ False) ∨ (p1 → p2)) ∧ ((p1 ∧ p2) ∧ (True → p7))) ∧ (((p1 ∧ p1) → (p0 → p3)) → False)) → ((((False ∨ p2) → False) ∧ ((p5 ∨ p0) → (p2 ∨ p4))) → (((p7 ∧ p0) → False) → ((p7 ∨ p1) ∨ (False → p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
        case inr assump_17 =>
          cases assump_15
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply Or.inl
              apply Or.inr
              exact assump_28


variable (p3 p5 p6 p2 p0 p7 : Prop)
theorem file27_68067 : (((((p5 ∧ False) → (True → False)) → False) ∧ (((p6 ∨ p6) ∨ (p0 ∧ p5)) → False)) → ((((True → p3) → (p2 → False)) ∧ ((p7 ∧ p6) → False)) → (((p0 → False) → (p7 → False)) → False))) := by
  intro assump_67
  intro assump_68
  intro assump_69
  cases assump_68
  case intro assump_72 assump_73 =>
    cases assump_67
    case intro assump_78 assump_79 =>
      have assump_99 : ((p5 ∧ False) → (True → False)) := by
        intro assump_86
        intro assump_87
        cases assump_86
        case intro assump_90 assump_91 =>
          apply False.elim assump_91
      let assump_85 := assump_78 assump_99
      apply False.elim assump_85


variable (p1 p3 p6 p4 p0 p2 p7 : Prop)
theorem file27_68771 : (((((p6 ∨ p2) ∨ (p1 → False)) → ((p0 ∧ p2) → (p0 ∨ p7))) ∨ (((p6 ∨ p3) → False) → False)) ∨ ((((True → p2) → (True → False)) ∧ ((p1 → False) ∨ (p7 → False))) ∧ (((p6 ∧ False) ∧ (p1 ∨ p4)) ∧ ((p4 ∧ p1) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inl
        exact assump_3
      case inr assump_12 =>
        apply Or.inl
        exact assump_3
    case inr assump_10 =>
      apply Or.inl
      exact assump_3


variable (p7 p6 p2 p1 : Prop)
theorem file27_69434 : (((((p7 → False) ∨ (p6 → False)) → False) ∧ (((True ∧ p7) ∨ (p2 ∧ p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : ((p7 → False) ∨ (p6 → False)) := by
      apply Or.inl
      intro assump_10
      have assump_22 : ((True ∧ p7) ∨ (p2 ∧ p1)) := by
        apply Or.inl
        apply And.intro
        apply True.intro
        exact assump_10
      let assump_14 := assump_3 assump_22
      apply False.elim assump_14
    let assump_9 := assump_2 assump_21
    apply False.elim assump_9


variable (p5 p4 p7 p0 p1 p6 p3 : Prop)
theorem file27_70052 : (((((False → p6) ∨ (p7 → False)) → False) → (((p3 → False) → (p1 → p4)) ∧ ((p6 ∨ p0) → False))) ∨ ((((p3 → False) ∨ (True ∧ p1)) ∨ ((p5 → p5) → (p0 ∧ p3))) ∨ (((p7 → False) → False) ∧ ((p4 ∨ p7) → (p5 ∨ p1))))) := by
  apply Or.inl
  intro assump_13
  apply And.intro
  intro assump_14
  intro assump_15
  have assump_54 : ((False → p6) ∨ (p7 → False)) := by
    apply Or.inl
    intro assump_23
    apply False.elim assump_23
  let assump_22 := assump_13 assump_54
  apply False.elim assump_22
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    have assump_55 : ((False → p6) ∨ (p7 → False)) := by
      apply Or.inl
      intro assump_37
      apply False.elim assump_37
    let assump_36 := assump_13 assump_55
    apply False.elim assump_36
  case inr assump_31 =>
    have assump_56 : ((False → p6) ∨ (p7 → False)) := by
      apply Or.inl
      intro assump_48
      apply False.elim assump_48
    let assump_47 := assump_13 assump_56
    apply False.elim assump_47


variable (p5 p2 p0 p1 p6 : Prop)
theorem file27_71094 : (((((p1 ∧ p5) → (True → p1)) → ((False → False) ∨ (False ∧ p1))) → False) → ((((p1 ∧ p2) → (False ∨ p2)) ∨ ((p6 → p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_33 : (((p1 ∧ p5) → (True → p1)) → ((False → False) ∨ (False ∧ p1))) := by
      intro assump_10
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    let assump_9 := assump_1 assump_33
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_34 : (((p1 ∧ p5) → (True → p1)) → ((False → False) ∨ (False ∧ p1))) := by
      intro assump_24
      apply Or.inl
      intro assump_27
      apply False.elim assump_27
    let assump_23 := assump_1 assump_34
    apply False.elim assump_23


variable (p3 p1 p7 p6 p0 p5 p4 : Prop)
theorem file27_71910 : (((((False ∧ p6) → (p7 ∧ p4)) ∨ ((p7 → p0) → (p3 ∧ p4))) → False) → ((((p3 → p7) → False) → ((p5 → True) → (True → p3))) ∧ (((p1 ∧ p4) ∧ (p1 → p1)) → ((True ∧ p5) ∧ (True → False))))) := by
  intro assump_20
  apply And.intro
  intro assump_21
  intro assump_22
  intro assump_23
  have assump_99 : (((False ∧ p6) → (p7 ∧ p4)) ∨ ((p7 → p0) → (p3 ∧ p4))) := by
    apply Or.inl
    intro assump_33
    apply And.intro
    cases assump_33
    case intro assump_34 assump_35 =>
      apply False.elim assump_34
    cases assump_33
    case intro assump_38 assump_39 =>
      apply False.elim assump_38
  let assump_32 := assump_20 assump_99
  apply False.elim assump_32
  intro assump_45
  apply And.intro
  apply And.intro
  apply True.intro
  cases assump_45
  case intro assump_46 assump_47 =>
    cases assump_46
    case intro assump_48 assump_49 =>
      have assump_100 : (((False ∧ p6) → (p7 ∧ p4)) ∨ ((p7 → p0) → (p3 ∧ p4))) := by
        apply Or.inl
        intro assump_59
        apply And.intro
        cases assump_59
        case intro assump_60 assump_61 =>
          apply False.elim assump_60
        cases assump_59
        case intro assump_64 assump_65 =>
          apply False.elim assump_64
      let assump_58 := assump_20 assump_100
      apply False.elim assump_58
  intro assump_71
  cases assump_45
  case intro assump_74 assump_75 =>
    cases assump_74
    case intro assump_76 assump_77 =>
      have assump_101 : (((False ∧ p6) → (p7 ∧ p4)) ∨ ((p7 → p0) → (p3 ∧ p4))) := by
        apply Or.inl
        intro assump_87
        apply And.intro
        cases assump_87
        case intro assump_88 assump_89 =>
          apply False.elim assump_88
        cases assump_87
        case intro assump_92 assump_93 =>
          apply False.elim assump_92
      let assump_86 := assump_20 assump_101
      apply False.elim assump_86


variable (p4 : Prop)
theorem file27_73811 : (((((True ∧ True) → (p4 ∧ False)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((True ∧ True) → (p4 ∧ False)) → False) := by
    intro assump_5
    have assump_18 : (True ∧ True) := by
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_5 assump_18
    let assump_9 := And.right assump_8
    apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p0 p3 p2 p6 p5 : Prop)
theorem file27_74322 : ((((((p6 ∨ p7) ∨ (p6 → False)) → ((p2 → False) ∨ (p3 ∨ p6))) → False) ∧ ((((p0 ∨ p5) ∨ (p0 ∨ p2)) → False) ∨ (((p6 → p6) → False) ∧ ((True ∨ p3) → False)))) → False) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      have assump_70 : (((p6 ∨ p7) ∨ (p6 → False)) → ((p2 → False) ∨ (p3 ∨ p6))) := by
        intro assump_19
        cases assump_19
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            apply Or.inl
            intro assump_26
            have assump_71 : ((p0 ∨ p5) ∨ (p0 ∨ p2)) := by
              apply Or.inr
              apply Or.inr
              exact assump_26
            let assump_31 := assump_13 assump_71
            apply False.elim assump_31
          case inr assump_23 =>
            apply Or.inl
            intro assump_37
            have assump_72 : ((p0 ∨ p5) ∨ (p0 ∨ p2)) := by
              apply Or.inr
              apply Or.inr
              exact assump_37
            let assump_42 := assump_13 assump_72
            apply False.elim assump_42
        case inr assump_21 =>
          apply Or.inl
          intro assump_48
          have assump_73 : ((p0 ∨ p5) ∨ (p0 ∨ p2)) := by
            apply Or.inr
            apply Or.inr
            exact assump_48
          let assump_53 := assump_13 assump_73
          apply False.elim assump_53
      let assump_18 := assump_9 assump_70
      apply False.elim assump_18
    case inr assump_14 =>
      cases assump_14
      case intro assump_60 assump_61 =>
        have assump_74 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_66 := assump_61 assump_74
        apply False.elim assump_66


variable (p3 p4 p1 p7 p2 p6 p0 : Prop)
theorem file27_76129 : (((((False ∨ p2) → (p3 → p2)) ∧ ((True → p4) ∧ (p6 ∨ p4))) ∨ (((p0 ∨ p1) → (p4 ∧ p6)) ∨ ((False ∨ p6) ∨ (p1 ∨ False)))) → ((((True ∨ p6) ∧ (True → False)) ∧ ((p1 ∨ p7) ∧ (p0 → False))) → (((True → False) ∨ (p6 ∨ p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_9
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_1
              case inl assump_26 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  cases assump_29
                  case intro assump_32 assump_33 =>
                    cases assump_33
                    case inl assump_36 =>
                      have assump_1046 : True := by
                        apply True.intro
                      let assump_46 := assump_11 assump_1046
                      apply False.elim assump_46
                    case inr assump_37 =>
                      have assump_1047 : True := by
                        apply True.intro
                      let assump_58 := assump_11 assump_1047
                      apply False.elim assump_58
              case inr assump_27 =>
                cases assump_27
                case inl assump_62 =>
                  have assump_1048 : True := by
                    apply True.intro
                  let assump_72 := assump_11 assump_1048
                  apply False.elim assump_72
                case inr assump_63 =>
                  cases assump_63
                  case inl assump_76 =>
                    cases assump_76
                    case inl assump_78 =>
                      apply False.elim assump_78
                    case inr assump_79 =>
                      have assump_1049 : True := by
                        apply True.intro
                      let assump_87 := assump_11 assump_1049
                      apply False.elim assump_87
                  case inr assump_77 =>
                    cases assump_77
                    case inl assump_91 =>
                      have assump_1050 : True := by
                        apply True.intro
                      let assump_98 := assump_11 assump_1050
                      apply False.elim assump_98
                    case inr assump_92 =>
                      apply False.elim assump_92
            case inr assump_21 =>
              cases assump_1
              case inl assump_108 =>
                cases assump_108
                case intro assump_110 assump_111 =>
                  cases assump_111
                  case intro assump_114 assump_115 =>
                    cases assump_115
                    case inl assump_118 =>
                      have assump_1051 : True := by
                        apply True.intro
                      let assump_128 := assump_11 assump_1051
                      apply False.elim assump_128
                    case inr assump_119 =>
                      have assump_1052 : True := by
                        apply True.intro
                      let assump_140 := assump_11 assump_1052
                      apply False.elim assump_140
              case inr assump_109 =>
                cases assump_109
                case inl assump_144 =>
                  have assump_1053 : True := by
                    apply True.intro
                  let assump_151 := assump_11 assump_1053
                  apply False.elim assump_151
                case inr assump_145 =>
                  cases assump_145
                  case inl assump_155 =>
                    cases assump_155
                    case inl assump_157 =>
                      apply False.elim assump_157
                    case inr assump_158 =>
                      have assump_1054 : True := by
                        apply True.intro
                      let assump_166 := assump_11 assump_1054
                      apply False.elim assump_166
                  case inr assump_156 =>
                    cases assump_156
                    case inl assump_170 =>
                      have assump_1055 : True := by
                        apply True.intro
                      let assump_177 := assump_11 assump_1055
                      apply False.elim assump_177
                    case inr assump_171 =>
                      apply False.elim assump_171
        case inr assump_13 =>
          cases assump_9
          case intro assump_187 assump_188 =>
            cases assump_187
            case inl assump_189 =>
              cases assump_1
              case inl assump_195 =>
                cases assump_195
                case intro assump_197 assump_198 =>
                  cases assump_198
                  case intro assump_201 assump_202 =>
                    cases assump_202
                    case inl assump_205 =>
                      have assump_1056 : True := by
                        apply True.intro
                      let assump_215 := assump_11 assump_1056
                      apply False.elim assump_215
                    case inr assump_206 =>
                      have assump_1057 : True := by
                        apply True.intro
                      let assump_227 := assump_11 assump_1057
                      apply False.elim assump_227
              case inr assump_196 =>
                cases assump_196
                case inl assump_231 =>
                  have assump_1058 : True := by
                    apply True.intro
                  let assump_241 := assump_11 assump_1058
                  apply False.elim assump_241
                case inr assump_232 =>
                  cases assump_232
                  case inl assump_245 =>
                    cases assump_245
                    case inl assump_247 =>
                      apply False.elim assump_247
                    case inr assump_248 =>
                      have assump_1059 : True := by
                        apply True.intro
                      let assump_256 := assump_11 assump_1059
                      apply False.elim assump_256
                  case inr assump_246 =>
                    cases assump_246
                    case inl assump_260 =>
                      have assump_1060 : True := by
                        apply True.intro
                      let assump_267 := assump_11 assump_1060
                      apply False.elim assump_267
                    case inr assump_261 =>
                      apply False.elim assump_261
            case inr assump_190 =>
              cases assump_1
              case inl assump_277 =>
                cases assump_277
                case intro assump_279 assump_280 =>
                  cases assump_280
                  case intro assump_283 assump_284 =>
                    cases assump_284
                    case inl assump_287 =>
                      have assump_1061 : True := by
                        apply True.intro
                      let assump_297 := assump_11 assump_1061
                      apply False.elim assump_297
                    case inr assump_288 =>
                      have assump_1062 : True := by
                        apply True.intro
                      let assump_309 := assump_11 assump_1062
                      apply False.elim assump_309
              case inr assump_278 =>
                cases assump_278
                case inl assump_313 =>
                  have assump_1063 : True := by
                    apply True.intro
                  let assump_320 := assump_11 assump_1063
                  apply False.elim assump_320
                case inr assump_314 =>
                  cases assump_314
                  case inl assump_324 =>
                    cases assump_324
                    case inl assump_326 =>
                      apply False.elim assump_326
                    case inr assump_327 =>
                      have assump_1064 : True := by
                        apply True.intro
                      let assump_335 := assump_11 assump_1064
                      apply False.elim assump_335
                  case inr assump_325 =>
                    cases assump_325
                    case inl assump_339 =>
                      have assump_1065 : True := by
                        apply True.intro
                      let assump_346 := assump_11 assump_1065
                      apply False.elim assump_346
                    case inr assump_340 =>
                      apply False.elim assump_340
  case inr assump_5 =>
    cases assump_5
    case inl assump_352 =>
      cases assump_2
      case intro assump_356 assump_357 =>
        cases assump_356
        case intro assump_358 assump_359 =>
          cases assump_358
          case inl assump_360 =>
            cases assump_357
            case intro assump_366 assump_367 =>
              cases assump_366
              case inl assump_368 =>
                cases assump_1
                case inl assump_374 =>
                  cases assump_374
                  case intro assump_376 assump_377 =>
                    cases assump_377
                    case intro assump_380 assump_381 =>
                      cases assump_381
                      case inl assump_384 =>
                        have assump_1066 : True := by
                          apply True.intro
                        let assump_394 := assump_359 assump_1066
                        apply False.elim assump_394
                      case inr assump_385 =>
                        have assump_1067 : True := by
                          apply True.intro
                        let assump_406 := assump_359 assump_1067
                        apply False.elim assump_406
                case inr assump_375 =>
                  cases assump_375
                  case inl assump_410 =>
                    have assump_1068 : True := by
                      apply True.intro
                    let assump_420 := assump_359 assump_1068
                    apply False.elim assump_420
                  case inr assump_411 =>
                    cases assump_411
                    case inl assump_424 =>
                      cases assump_424
                      case inl assump_426 =>
                        apply False.elim assump_426
                      case inr assump_427 =>
                        have assump_1069 : True := by
                          apply True.intro
                        let assump_435 := assump_359 assump_1069
                        apply False.elim assump_435
                    case inr assump_425 =>
                      cases assump_425
                      case inl assump_439 =>
                        have assump_1070 : True := by
                          apply True.intro
                        let assump_446 := assump_359 assump_1070
                        apply False.elim assump_446
                      case inr assump_440 =>
                        apply False.elim assump_440
              case inr assump_369 =>
                cases assump_1
                case inl assump_456 =>
                  cases assump_456
                  case intro assump_458 assump_459 =>
                    cases assump_459
                    case intro assump_462 assump_463 =>
                      cases assump_463
                      case inl assump_466 =>
                        have assump_1071 : True := by
                          apply True.intro
                        let assump_476 := assump_359 assump_1071
                        apply False.elim assump_476
                      case inr assump_467 =>
                        have assump_1072 : True := by
                          apply True.intro
                        let assump_488 := assump_359 assump_1072
                        apply False.elim assump_488
                case inr assump_457 =>
                  cases assump_457
                  case inl assump_492 =>
                    have assump_1073 : True := by
                      apply True.intro
                    let assump_499 := assump_359 assump_1073
                    apply False.elim assump_499
                  case inr assump_493 =>
                    cases assump_493
                    case inl assump_503 =>
                      cases assump_503
                      case inl assump_505 =>
                        apply False.elim assump_505
                      case inr assump_506 =>
                        have assump_1074 : True := by
                          apply True.intro
                        let assump_514 := assump_359 assump_1074
                        apply False.elim assump_514
                    case inr assump_504 =>
                      cases assump_504
                      case inl assump_518 =>
                        have assump_1075 : True := by
                          apply True.intro
                        let assump_525 := assump_359 assump_1075
                        apply False.elim assump_525
                      case inr assump_519 =>
                        apply False.elim assump_519
          case inr assump_361 =>
            cases assump_357
            case intro assump_535 assump_536 =>
              cases assump_535
              case inl assump_537 =>
                cases assump_1
                case inl assump_543 =>
                  cases assump_543
                  case intro assump_545 assump_546 =>
                    cases assump_546
                    case intro assump_549 assump_550 =>
                      cases assump_550
                      case inl assump_553 =>
                        have assump_1076 : True := by
                          apply True.intro
                        let assump_563 := assump_359 assump_1076
                        apply False.elim assump_563
                      case inr assump_554 =>
                        have assump_1077 : True := by
                          apply True.intro
                        let assump_575 := assump_359 assump_1077
                        apply False.elim assump_575
                case inr assump_544 =>
                  cases assump_544
                  case inl assump_579 =>
                    have assump_1078 : True := by
                      apply True.intro
                    let assump_589 := assump_359 assump_1078
                    apply False.elim assump_589
                  case inr assump_580 =>
                    cases assump_580
                    case inl assump_593 =>
                      cases assump_593
                      case inl assump_595 =>
                        apply False.elim assump_595
                      case inr assump_596 =>
                        have assump_1079 : True := by
                          apply True.intro
                        let assump_604 := assump_359 assump_1079
                        apply False.elim assump_604
                    case inr assump_594 =>
                      cases assump_594
                      case inl assump_608 =>
                        have assump_1080 : True := by
                          apply True.intro
                        let assump_615 := assump_359 assump_1080
                        apply False.elim assump_615
                      case inr assump_609 =>
                        apply False.elim assump_609
              case inr assump_538 =>
                cases assump_1
                case inl assump_625 =>
                  cases assump_625
                  case intro assump_627 assump_628 =>
                    cases assump_628
                    case intro assump_631 assump_632 =>
                      cases assump_632
                      case inl assump_635 =>
                        have assump_1081 : True := by
                          apply True.intro
                        let assump_645 := assump_359 assump_1081
                        apply False.elim assump_645
                      case inr assump_636 =>
                        have assump_1082 : True := by
                          apply True.intro
                        let assump_657 := assump_359 assump_1082
                        apply False.elim assump_657
                case inr assump_626 =>
                  cases assump_626
                  case inl assump_661 =>
                    have assump_1083 : True := by
                      apply True.intro
                    let assump_668 := assump_359 assump_1083
                    apply False.elim assump_668
                  case inr assump_662 =>
                    cases assump_662
                    case inl assump_672 =>
                      cases assump_672
                      case inl assump_674 =>
                        apply False.elim assump_674
                      case inr assump_675 =>
                        have assump_1084 : True := by
                          apply True.intro
                        let assump_683 := assump_359 assump_1084
                        apply False.elim assump_683
                    case inr assump_673 =>
                      cases assump_673
                      case inl assump_687 =>
                        have assump_1085 : True := by
                          apply True.intro
                        let assump_694 := assump_359 assump_1085
                        apply False.elim assump_694
                      case inr assump_688 =>
                        apply False.elim assump_688
    case inr assump_353 =>
      cases assump_2
      case intro assump_702 assump_703 =>
        cases assump_702
        case intro assump_704 assump_705 =>
          cases assump_704
          case inl assump_706 =>
            cases assump_703
            case intro assump_712 assump_713 =>
              cases assump_712
              case inl assump_714 =>
                cases assump_1
                case inl assump_720 =>
                  cases assump_720
                  case intro assump_722 assump_723 =>
                    cases assump_723
                    case intro assump_726 assump_727 =>
                      cases assump_727
                      case inl assump_730 =>
                        have assump_1086 : True := by
                          apply True.intro
                        let assump_740 := assump_705 assump_1086
                        apply False.elim assump_740
                      case inr assump_731 =>
                        have assump_1087 : True := by
                          apply True.intro
                        let assump_752 := assump_705 assump_1087
                        apply False.elim assump_752
                case inr assump_721 =>
                  cases assump_721
                  case inl assump_756 =>
                    have assump_1088 : True := by
                      apply True.intro
                    let assump_766 := assump_705 assump_1088
                    apply False.elim assump_766
                  case inr assump_757 =>
                    cases assump_757
                    case inl assump_770 =>
                      cases assump_770
                      case inl assump_772 =>
                        apply False.elim assump_772
                      case inr assump_773 =>
                        have assump_1089 : True := by
                          apply True.intro
                        let assump_781 := assump_705 assump_1089
                        apply False.elim assump_781
                    case inr assump_771 =>
                      cases assump_771
                      case inl assump_785 =>
                        have assump_1090 : True := by
                          apply True.intro
                        let assump_792 := assump_705 assump_1090
                        apply False.elim assump_792
                      case inr assump_786 =>
                        apply False.elim assump_786
              case inr assump_715 =>
                cases assump_1
                case inl assump_802 =>
                  cases assump_802
                  case intro assump_804 assump_805 =>
                    cases assump_805
                    case intro assump_808 assump_809 =>
                      cases assump_809
                      case inl assump_812 =>
                        have assump_1091 : True := by
                          apply True.intro
                        let assump_822 := assump_705 assump_1091
                        apply False.elim assump_822
                      case inr assump_813 =>
                        have assump_1092 : True := by
                          apply True.intro
                        let assump_834 := assump_705 assump_1092
                        apply False.elim assump_834
                case inr assump_803 =>
                  cases assump_803
                  case inl assump_838 =>
                    have assump_1093 : True := by
                      apply True.intro
                    let assump_845 := assump_705 assump_1093
                    apply False.elim assump_845
                  case inr assump_839 =>
                    cases assump_839
                    case inl assump_849 =>
                      cases assump_849
                      case inl assump_851 =>
                        apply False.elim assump_851
                      case inr assump_852 =>
                        have assump_1094 : True := by
                          apply True.intro
                        let assump_860 := assump_705 assump_1094
                        apply False.elim assump_860
                    case inr assump_850 =>
                      cases assump_850
                      case inl assump_864 =>
                        have assump_1095 : True := by
                          apply True.intro
                        let assump_871 := assump_705 assump_1095
                        apply False.elim assump_871
                      case inr assump_865 =>
                        apply False.elim assump_865
          case inr assump_707 =>
            cases assump_703
            case intro assump_881 assump_882 =>
              cases assump_881
              case inl assump_883 =>
                cases assump_1
                case inl assump_889 =>
                  cases assump_889
                  case intro assump_891 assump_892 =>
                    cases assump_892
                    case intro assump_895 assump_896 =>
                      cases assump_896
                      case inl assump_899 =>
                        have assump_1096 : True := by
                          apply True.intro
                        let assump_909 := assump_705 assump_1096
                        apply False.elim assump_909
                      case inr assump_900 =>
                        have assump_1097 : True := by
                          apply True.intro
                        let assump_921 := assump_705 assump_1097
                        apply False.elim assump_921
                case inr assump_890 =>
                  cases assump_890
                  case inl assump_925 =>
                    have assump_1098 : True := by
                      apply True.intro
                    let assump_935 := assump_705 assump_1098
                    apply False.elim assump_935
                  case inr assump_926 =>
                    cases assump_926
                    case inl assump_939 =>
                      cases assump_939
                      case inl assump_941 =>
                        apply False.elim assump_941
                      case inr assump_942 =>
                        have assump_1099 : True := by
                          apply True.intro
                        let assump_950 := assump_705 assump_1099
                        apply False.elim assump_950
                    case inr assump_940 =>
                      cases assump_940
                      case inl assump_954 =>
                        have assump_1100 : True := by
                          apply True.intro
                        let assump_961 := assump_705 assump_1100
                        apply False.elim assump_961
                      case inr assump_955 =>
                        apply False.elim assump_955
              case inr assump_884 =>
                cases assump_1
                case inl assump_971 =>
                  cases assump_971
                  case intro assump_973 assump_974 =>
                    cases assump_974
                    case intro assump_977 assump_978 =>
                      cases assump_978
                      case inl assump_981 =>
                        have assump_1101 : True := by
                          apply True.intro
                        let assump_991 := assump_705 assump_1101
                        apply False.elim assump_991
                      case inr assump_982 =>
                        have assump_1102 : True := by
                          apply True.intro
                        let assump_1003 := assump_705 assump_1102
                        apply False.elim assump_1003
                case inr assump_972 =>
                  cases assump_972
                  case inl assump_1007 =>
                    have assump_1103 : True := by
                      apply True.intro
                    let assump_1014 := assump_705 assump_1103
                    apply False.elim assump_1014
                  case inr assump_1008 =>
                    cases assump_1008
                    case inl assump_1018 =>
                      cases assump_1018
                      case inl assump_1020 =>
                        apply False.elim assump_1020
                      case inr assump_1021 =>
                        have assump_1104 : True := by
                          apply True.intro
                        let assump_1029 := assump_705 assump_1104
                        apply False.elim assump_1029
                    case inr assump_1019 =>
                      cases assump_1019
                      case inl assump_1033 =>
                        have assump_1105 : True := by
                          apply True.intro
                        let assump_1040 := assump_705 assump_1105
                        apply False.elim assump_1040
                      case inr assump_1034 =>
                        apply False.elim assump_1034


variable (p3 p6 p1 : Prop)
theorem file27_102840 : ((((((True ∨ p1) ∨ (p3 ∨ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p1) ∨ (p3 ∨ p6)) → False) → False) := by
    intro assump_5
    have assump_16 : ((True ∨ p1) ∨ (p3 ∨ p6)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p2 p5 p1 p3 p0 : Prop)
theorem file27_103327 : (((((p1 → False) → False) → ((p2 → p0) ∧ (p6 ∧ p1))) → (((p1 ∧ False) → (p3 → p1)) → ((False ∨ False) → (p0 ∨ p1)))) ∨ ((((p2 → False) → (p5 ∨ p6)) → ((p5 → p0) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply False.elim assump_4
  case inr assump_5 =>
    apply False.elim assump_5


variable (p1 p4 p2 : Prop)
theorem file27_103754 : ((((((p1 ∧ False) → False) → False) → (((p2 ∨ p4) ∨ (False → False)) → ((False → False) → False))) → False) → False) := by
  intro assump_1
  have assump_62 : ((((p1 ∧ False) → False) → False) → (((p2 ∨ p4) ∨ (False → False)) → ((False → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        have assump_63 : ((p1 ∧ False) → False) := by
          intro assump_19
          cases assump_19
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
        let assump_18 := assump_5 assump_63
        apply False.elim assump_18
      case inr assump_13 =>
        have assump_64 : ((p1 ∧ False) → False) := by
          intro assump_34
          cases assump_34
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
        let assump_33 := assump_5 assump_64
        apply False.elim assump_33
    case inr assump_11 =>
      have assump_65 : ((p1 ∧ False) → False) := by
        intro assump_49
        cases assump_49
        case intro assump_50 assump_51 =>
          apply False.elim assump_51
      let assump_48 := assump_5 assump_65
      apply False.elim assump_48
  let assump_4 := assump_1 assump_62
  apply False.elim assump_4


variable (p2 p1 p0 p4 : Prop)
theorem file27_105131 : (((((p2 ∧ p4) ∧ (p1 → False)) → ((p0 ∨ p2) ∧ (True → p4))) → False) → False) := by
  intro assump_1
  have assump_32 : (((p2 ∧ p4) ∧ (p1 → False)) → ((p0 ∨ p2) ∧ (True → p4))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inr
        exact assump_8
    intro assump_16
    cases assump_5
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        exact assump_22
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p5 p4 p0 p1 : Prop)
theorem file27_105792 : (((((p5 → True) ∨ (True → False)) → False) → False) ∨ ((((False → p5) ∨ (p5 ∨ p0)) → False) ∧ (((True → p1) → False) → ((p0 → p1) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p5 → True) ∨ (True → False)) := by
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p5 p0 p7 : Prop)
theorem file27_106206 : (((((p0 ∨ p5) → (p7 ∨ p0)) → ((False ∧ False) → (False → False))) → False) → False) := by
  intro assump_11
  have assump_23 : (((p0 ∨ p5) → (p7 ∨ p0)) → ((False ∧ False) → (False → False))) := by
    intro assump_15
    intro assump_16
    intro assump_17
    apply False.elim assump_17
  let assump_14 := assump_11 assump_23
  apply False.elim assump_14


variable (p0 p1 p6 p4 p3 : Prop)
theorem file27_106619 : ((((((p0 → False) ∧ (p0 ∧ p0)) → ((p6 ∧ p1) ∧ (p1 ∨ False))) ∨ (((p6 → False) → False) ∨ ((p3 → p6) ∧ (p0 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_57 : ((((p0 → False) ∧ (p0 ∧ p0)) → ((p6 ∧ p1) ∧ (p1 ∨ False))) ∨ (((p6 → False) → False) ∨ ((p3 → p6) ∧ (p0 ∧ p4)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_58 : p0 := by
          exact assump_11
        let assump_18 := assump_6 assump_58
        apply False.elim assump_18
    cases assump_5
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        have assump_59 : p0 := by
          exact assump_27
        let assump_34 := assump_22 assump_59
        apply False.elim assump_34
    cases assump_5
    case intro assump_38 assump_39 =>
      cases assump_39
      case intro assump_42 assump_43 =>
        have assump_60 : p0 := by
          exact assump_43
        let assump_50 := assump_38 assump_60
        apply False.elim assump_50
  let assump_4 := assump_1 assump_57
  apply False.elim assump_4


variable (p3 p6 p5 p2 p1 p7 : Prop)
theorem file27_107887 : ((((((p2 ∧ p6) ∨ (p7 → False)) ∧ ((p3 → False) ∧ (p3 → p3))) → (((p6 → False) → (p7 → p5)) ∨ ((p2 ∧ p2) → (p5 → p1)))) → False) → False) := by
  intro assump_1
  have assump_57 : ((((p2 ∧ p6) ∨ (p7 → False)) ∧ ((p3 → False) ∧ (p3 → p3))) → (((p6 → False) → (p7 → p5)) ∨ ((p2 ∧ p2) → (p5 → p1)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            apply Or.inl
            intro assump_22
            intro assump_23
            have assump_58 : p6 := by
              exact assump_11
            let assump_28 := assump_22 assump_58
            apply False.elim assump_28
      case inr assump_9 =>
        cases assump_7
        case intro assump_34 assump_35 =>
          apply Or.inl
          intro assump_40
          intro assump_41
          have assump_59 : p7 := by
            exact assump_41
          let assump_50 := assump_9 assump_59
          apply False.elim assump_50
  let assump_4 := assump_1 assump_57
  apply False.elim assump_4


variable (p0 p4 p6 p5 : Prop)
theorem file27_109115 : ((((((p6 ∨ p0) ∧ (True ∧ False)) ∧ ((p5 → False) ∨ (p4 → p5))) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p6 ∨ p0) ∧ (True ∧ False)) ∧ ((p5 → False) ∨ (p4 → p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
        case inr assump_11 =>
          cases assump_9
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p3 p2 p6 p5 p7 : Prop)
theorem file27_109880 : (((((False ∧ p3) ∧ (p6 → False)) ∧ ((p3 → False) ∨ (p3 ∧ p2))) ∧ (((p5 → p2) → False) → False)) ∨ ((((True ∨ p2) → (False ∧ p7)) → False) ∨ (((p1 ∧ False) ∧ (True → p7)) → False))) := by
  apply Or.inr
  apply Or.inl
  intro assump_1
  have assump_9 : (True ∨ p2) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_9
  let assump_5 := And.left assump_4
  apply False.elim assump_5


variable (p6 p2 p7 : Prop)
theorem file27_110339 : ((((((p2 ∧ p7) → (False → p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p2 ∧ p7) → (False → p6)) → False) → False) := by
    intro assump_5
    have assump_20 : ((p2 ∧ p7) → (False → p6)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p0 p2 p1 p4 p5 p7 p3 : Prop)
theorem file27_110847 : (((((p0 → False) ∨ (True → False)) → False) ∨ (((False → p0) ∨ (p7 → False)) ∧ ((p2 → False) → False))) → ((((p1 ∧ p3) → False) → False) → (((p4 ∧ p3) → (p7 → False)) → ((p5 ∧ p4) → (True ∨ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_1
    case inl assump_15 =>
      apply Or.inl
      apply True.intro
    case inr assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        cases assump_19
        case inl assump_21 =>
          apply Or.inl
          apply True.intro
        case inr assump_22 =>
          apply Or.inl
          apply True.intro


variable (p3 p7 p5 p6 p1 p2 p4 : Prop)
theorem file27_111592 : ((((((p6 ∧ p6) ∨ (p1 → True)) ∨ ((False ∧ p6) → (p2 ∨ p4))) ∧ (((p4 ∧ p3) ∨ (True ∨ True)) → False)) ∧ ((((p7 ∧ p5) ∧ (False ∧ p3)) → False) ∨ (((p3 → True) → (p3 ∧ p5)) ∧ ((False → p7) ∨ (p2 ∧ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_3
            case inl assump_18 =>
              have assump_158 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
                apply Or.inr
                apply Or.inl
                apply True.intro
              let assump_23 := assump_5 assump_158
              apply False.elim assump_23
            case inr assump_19 =>
              cases assump_19
              case intro assump_27 assump_28 =>
                cases assump_28
                case inl assump_31 =>
                  have assump_159 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                  let assump_41 := assump_5 assump_159
                  apply False.elim assump_41
                case inr assump_32 =>
                  cases assump_32
                  case intro assump_45 assump_46 =>
                    have assump_160 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
                      apply Or.inr
                      apply Or.inl
                      apply True.intro
                    let assump_58 := assump_5 assump_160
                    apply False.elim assump_58
        case inr assump_9 =>
          cases assump_3
          case inl assump_66 =>
            have assump_161 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_71 := assump_5 assump_161
            apply False.elim assump_71
          case inr assump_67 =>
            cases assump_67
            case intro assump_75 assump_76 =>
              cases assump_76
              case inl assump_79 =>
                have assump_162 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_89 := assump_5 assump_162
                apply False.elim assump_89
              case inr assump_80 =>
                cases assump_80
                case intro assump_93 assump_94 =>
                  have assump_163 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                  let assump_106 := assump_5 assump_163
                  apply False.elim assump_106
      case inr assump_7 =>
        cases assump_3
        case inl assump_114 =>
          have assump_164 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_119 := assump_5 assump_164
          apply False.elim assump_119
        case inr assump_115 =>
          cases assump_115
          case intro assump_123 assump_124 =>
            cases assump_124
            case inl assump_127 =>
              have assump_165 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
                apply Or.inr
                apply Or.inl
                apply True.intro
              let assump_137 := assump_5 assump_165
              apply False.elim assump_137
            case inr assump_128 =>
              cases assump_128
              case intro assump_141 assump_142 =>
                have assump_166 : ((p4 ∧ p3) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_154 := assump_5 assump_166
                apply False.elim assump_154


variable (p4 p1 p3 p5 p0 p2 : Prop)
theorem file27_115590 : (((((True → False) → (p4 ∨ True)) → False) → False) ∨ ((((p3 ∧ p3) → False) ∧ ((p1 ∨ False) → False)) → (((p3 → p2) → (p4 ∧ p2)) ∧ ((p0 ∨ p2) ∧ (p5 ∨ p1))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((True → False) → (p4 ∨ True)) := by
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p0 p4 p7 : Prop)
theorem file27_116018 : ((((((p7 ∧ p0) ∧ (p4 ∧ p5)) → False) → False) ∧ ((((p7 ∨ True) → False) → ((p5 ∧ p4) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : (((p7 ∨ True) → False) → ((p5 ∧ p4) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_27 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_19 := assump_9 assump_27
        apply False.elim assump_19
    let assump_8 := assump_3 assump_26
    apply False.elim assump_8


variable (p3 p7 p5 p2 p0 : Prop)
theorem file27_116682 : ((((((p2 ∧ p0) ∨ (p5 ∧ p0)) → ((p2 → p3) → False)) → (((p7 → p0) ∧ (p3 → False)) → ((True → False) → (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p2 ∧ p0) ∨ (p5 ∧ p0)) → ((p2 → p3) → False)) → (((p7 → p0) ∧ (p3 → False)) → ((True → False) → (p7 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      have assump_33 : True := by
        apply True.intro
      let assump_25 := assump_7 assump_33
      apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 p7 p5 p4 p2 p3 p6 p0 : Prop)
theorem file27_117378 : (((((p0 ∧ p4) → (False → p4)) ∨ ((p1 ∧ p5) ∨ (False → False))) → False) → ((((p4 → p1) → (p6 → p3)) ∨ ((p2 ∨ p7) → (True → False))) ∨ (((False → p2) → (p4 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_20 : (((p0 ∧ p4) → (False → p4)) ∨ ((p1 ∧ p5) ∨ (False → False))) := by
    apply Or.inl
    intro assump_13
    intro assump_14
    apply False.elim assump_14
  let assump_12 := assump_1 assump_20
  apply False.elim assump_12


variable (p2 p5 p0 p3 p7 p1 p4 p6 : Prop)
theorem file27_117948 : (((((True ∨ p6) ∧ (False ∧ p6)) ∧ ((p1 ∨ p0) → (p6 → False))) ∧ (((p5 ∧ False) → (p1 → p7)) ∨ ((False → p7) → False))) → ((((p1 ∨ p1) ∧ (True → False)) ∧ ((p2 → p1) ∨ (p3 ∧ p4))) ∧ (((p4 ∨ p0) ∧ (True → False)) ∨ ((False ∨ p3) → (p5 → p7))))) := by
  intro assump_11
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_17
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
        case inr assump_19 =>
          cases assump_17
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
  intro assump_32
  cases assump_11
  case intro assump_35 assump_36 =>
    cases assump_35
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_39
        case inl assump_41 =>
          cases assump_40
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
        case inr assump_42 =>
          cases assump_40
          case intro assump_51 assump_52 =>
            apply False.elim assump_51
  cases assump_11
  case intro assump_55 assump_56 =>
    cases assump_55
    case intro assump_57 assump_58 =>
      cases assump_57
      case intro assump_59 assump_60 =>
        cases assump_59
        case inl assump_61 =>
          cases assump_60
          case intro assump_65 assump_66 =>
            apply False.elim assump_65
        case inr assump_62 =>
          cases assump_60
          case intro assump_71 assump_72 =>
            apply False.elim assump_71
  cases assump_11
  case intro assump_75 assump_76 =>
    cases assump_75
    case intro assump_77 assump_78 =>
      cases assump_77
      case intro assump_79 assump_80 =>
        cases assump_79
        case inl assump_81 =>
          cases assump_80
          case intro assump_85 assump_86 =>
            apply False.elim assump_85
        case inr assump_82 =>
          cases assump_80
          case intro assump_91 assump_92 =>
            apply False.elim assump_91


variable (p7 p5 p6 p4 p1 p3 p0 : Prop)
theorem file27_120254 : (((((p1 → False) → False) ∧ ((p6 ∧ p4) ∨ (p7 → False))) ∧ (((p1 → False) → (p6 ∧ p6)) → False)) → ((((p3 ∨ p4) ∧ (True ∧ p6)) ∧ ((p1 → p5) ∨ (p0 → True))) → (((False → p5) ∧ (True → p0)) → ((p5 ∧ True) → False)))) := by
  intro assump_11
  intro assump_12
  intro assump_13
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_13
    case intro assump_21 assump_22 =>
      cases assump_12
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_29
          case inl assump_31 =>
            cases assump_30
            case intro assump_35 assump_36 =>
              cases assump_28
              case inl assump_41 =>
                cases assump_11
                case intro assump_45 assump_46 =>
                  cases assump_45
                  case intro assump_47 assump_48 =>
                    cases assump_48
                    case inl assump_51 =>
                      cases assump_51
                      case intro assump_53 assump_54 =>
                        have assump_213 : ((p1 → False) → (p6 ∧ p6)) := by
                          intro assump_62
                          apply And.intro
                          exact assump_53
                          exact assump_53
                        let assump_61 := assump_46 assump_213
                        apply False.elim assump_61
                    case inr assump_52 =>
                      have assump_214 : ((p1 → False) → (p6 ∧ p6)) := by
                        intro assump_75
                        apply And.intro
                        exact assump_36
                        exact assump_36
                      let assump_74 := assump_46 assump_214
                      apply False.elim assump_74
              case inr assump_42 =>
                cases assump_11
                case intro assump_85 assump_86 =>
                  cases assump_85
                  case intro assump_87 assump_88 =>
                    cases assump_88
                    case inl assump_91 =>
                      cases assump_91
                      case intro assump_93 assump_94 =>
                        have assump_215 : ((p1 → False) → (p6 ∧ p6)) := by
                          intro assump_102
                          apply And.intro
                          exact assump_93
                          exact assump_93
                        let assump_101 := assump_86 assump_215
                        apply False.elim assump_101
                    case inr assump_92 =>
                      have assump_216 : ((p1 → False) → (p6 ∧ p6)) := by
                        intro assump_115
                        apply And.intro
                        exact assump_36
                        exact assump_36
                      let assump_114 := assump_86 assump_216
                      apply False.elim assump_114
          case inr assump_32 =>
            cases assump_30
            case intro assump_125 assump_126 =>
              cases assump_28
              case inl assump_131 =>
                cases assump_11
                case intro assump_135 assump_136 =>
                  cases assump_135
                  case intro assump_137 assump_138 =>
                    cases assump_138
                    case inl assump_141 =>
                      cases assump_141
                      case intro assump_143 assump_144 =>
                        have assump_217 : ((p1 → False) → (p6 ∧ p6)) := by
                          intro assump_152
                          apply And.intro
                          exact assump_143
                          exact assump_143
                        let assump_151 := assump_136 assump_217
                        apply False.elim assump_151
                    case inr assump_142 =>
                      have assump_218 : ((p1 → False) → (p6 ∧ p6)) := by
                        intro assump_165
                        apply And.intro
                        exact assump_126
                        exact assump_126
                      let assump_164 := assump_136 assump_218
                      apply False.elim assump_164
              case inr assump_132 =>
                cases assump_11
                case intro assump_175 assump_176 =>
                  cases assump_175
                  case intro assump_177 assump_178 =>
                    cases assump_178
                    case inl assump_181 =>
                      cases assump_181
                      case intro assump_183 assump_184 =>
                        have assump_219 : ((p1 → False) → (p6 ∧ p6)) := by
                          intro assump_192
                          apply And.intro
                          exact assump_183
                          exact assump_183
                        let assump_191 := assump_176 assump_219
                        apply False.elim assump_191
                    case inr assump_182 =>
                      have assump_220 : ((p1 → False) → (p6 ∧ p6)) := by
                        intro assump_205
                        apply And.intro
                        exact assump_126
                        exact assump_126
                      let assump_204 := assump_176 assump_220
                      apply False.elim assump_204


variable (p4 p5 p7 p0 p1 p2 p6 : Prop)
theorem file27_125667 : ((((((p4 → False) ∧ (p2 ∨ p7)) → False) ∧ (((p5 ∧ False) → (p1 → p6)) → False)) ∨ ((((p0 → p1) ∨ (p6 → p0)) → False) ∧ (((p6 → False) → (p2 → False)) ∧ ((True ∨ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_38 : ((p5 ∧ False) → (p1 → p6)) := by
        intro assump_11
        intro assump_12
        cases assump_11
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
      let assump_10 := assump_5 assump_38
      apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case intro assump_24 assump_25 =>
      cases assump_25
      case intro assump_28 assump_29 =>
        have assump_39 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_34 := assump_29 assump_39
        apply False.elim assump_34


variable (p0 p1 p2 : Prop)
theorem file27_126619 : (((((p1 ∨ False) → (p0 → p2)) → ((p0 → p0) ∧ (False → False))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p1 ∨ False) → (p0 → p2)) → ((p0 → p0) ∧ (False → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    exact assump_6
    intro assump_11
    apply False.elim assump_11
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p6 p5 p0 p2 p7 p4 : Prop)
theorem file27_127062 : (((((p2 → True) ∧ (p6 → False)) ∧ ((False ∧ False) ∧ (p0 → False))) ∧ (((p6 → False) → (p0 ∨ p4)) ∧ ((p7 ∧ p2) → (True → False)))) → ((((p4 → p6) → False) ∧ ((True ∨ p4) → (True ∧ p4))) ∧ (((p5 ∧ p5) → False) → False))) := by
  intro assump_5
  apply And.intro
  apply And.intro
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_12
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
  intro assump_25
  apply And.intro
  apply True.intro
  cases assump_25
  case inl assump_26 =>
    cases assump_5
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          cases assump_33
          case intro assump_40 assump_41 =>
            cases assump_40
            case intro assump_42 assump_43 =>
              apply False.elim assump_42
  case inr assump_27 =>
    cases assump_5
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_51
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              apply False.elim assump_60
  intro assump_64
  cases assump_5
  case intro assump_67 assump_68 =>
    cases assump_67
    case intro assump_69 assump_70 =>
      cases assump_69
      case intro assump_71 assump_72 =>
        cases assump_70
        case intro assump_77 assump_78 =>
          cases assump_77
          case intro assump_79 assump_80 =>
            apply False.elim assump_79


variable (p0 p2 p1 p3 p6 : Prop)
theorem file27_128988 : (((((p1 → False) → (p1 → p0)) → ((p6 ∨ p6) ∧ (p2 ∧ p3))) → (((p2 ∧ False) ∧ (p2 → False)) ∨ ((False ∧ True) → False))) ∨ ((((p6 → p0) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p7 p4 p5 p0 p6 : Prop)
theorem file27_129358 : (((((False → False) → (p4 → False)) ∧ ((p4 ∨ p0) → False)) ∧ (((p7 ∨ p5) ∧ (p7 → False)) → False)) → ((((p4 → p4) → False) → False) ∨ (((p6 ∧ False) → False) ∧ ((False → False) → (p5 → p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      have assump_22 : (p4 → p4) := by
        intro assump_16
        exact assump_16
      let assump_15 := assump_12 assump_22
      apply False.elim assump_15


variable (p5 p1 p3 p0 p4 : Prop)
theorem file27_129941 : (((((False → False) ∧ (p3 → False)) → False) → (((p5 ∨ p0) ∨ (p1 → p1)) ∨ ((p1 ∧ p4) ∧ (p3 ∧ p4)))) ∨ ((((True ∧ p4) ∨ (True → p3)) ∨ ((p3 ∨ True) → (p3 → p5))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  exact assump_4


variable (p3 p2 p4 p1 p6 p7 : Prop)
theorem file27_130274 : ((((((p4 → p6) ∨ (p1 ∧ p6)) → ((p1 → False) → False)) ∧ (((True → p4) → (p2 ∧ p3)) → ((False ∨ True) ∧ (p2 → p1)))) ∧ ((((p6 ∨ p6) ∨ (False → p7)) → False) ∧ (((p6 → False) ∧ (p3 → True)) ∧ ((p1 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            have assump_29 : (p1 → True) := by
              intro assump_25
              apply True.intro
            let assump_24 := assump_15 assump_29
            apply False.elim assump_24


variable (p1 p3 p5 p0 p4 : Prop)
theorem file27_131077 : ((((((p3 → False) ∨ (p1 → p5)) → ((True ∨ p5) ∨ (p3 ∧ False))) ∨ (((True ∨ p0) → (p3 ∧ False)) ∧ ((p5 ∨ p4) ∨ (True ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p3 → False) ∨ (p1 → p5)) → ((True ∨ p5) ∨ (p3 ∧ False))) ∨ (((True ∨ p0) → (p3 ∧ False)) ∧ ((p5 ∨ p4) ∨ (True ∨ p0)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p3 p1 p6 p5 p2 p4 : Prop)
theorem file27_131746 : (((((p3 → False) → (True → False)) ∨ ((p0 → True) ∨ (p5 → True))) ∧ (((True ∧ False) → (p4 ∨ p5)) → False)) → ((((p1 ∨ True) ∨ (p3 ∨ p1)) → ((p6 ∧ p2) → (p5 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_56 : ((True ∧ False) → (p4 ∨ p5)) := by
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
      let assump_13 := assump_6 assump_56
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case inl assump_24 =>
        have assump_57 : ((True ∧ False) → (p4 ∨ p5)) := by
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
        let assump_30 := assump_6 assump_57
        apply False.elim assump_30
      case inr assump_25 =>
        have assump_58 : ((True ∧ False) → (p4 ∨ p5)) := by
          intro assump_46
          cases assump_46
          case intro assump_47 assump_48 =>
            apply False.elim assump_48
        let assump_45 := assump_6 assump_58
        apply False.elim assump_45


variable (p2 p0 p1 p5 p7 p4 p3 : Prop)
theorem file27_133032 : (((((p3 ∧ p4) → (p1 ∨ p3)) ∨ ((p2 → p2) ∨ (p5 ∧ p1))) → (((True → False) → (p1 ∨ True)) ∨ ((p2 → True) → False))) ∨ ((((p0 → False) → (p7 ∧ p1)) ∨ ((p4 ∧ p1) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_9 =>
      apply Or.inl
      intro assump_13
      apply Or.inr
      apply True.intro
    case inr assump_10 =>
      cases assump_10
      case intro assump_16 assump_17 =>
        apply Or.inl
        intro assump_22
        apply Or.inl
        exact assump_17


variable (p0 p5 p3 p7 p2 p6 : Prop)
theorem file27_133750 : (((((p0 → p2) ∨ (p0 → False)) ∧ ((True ∧ p7) → (p0 → p5))) → False) → ((((True → p6) → (p3 ∨ p5)) → ((True → False) → (False → p0))) ∨ (((p7 ∨ p0) → (False ∨ False)) → ((p0 → True) ∧ (p5 ∨ p7))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p6 p4 p0 p3 p2 p5 : Prop)
theorem file27_134124 : ((((((p0 ∧ p0) → False) ∧ ((p3 → False) ∨ (p2 → False))) → (((p6 ∧ p0) ∨ (False → False)) ∨ ((p4 → False) ∧ (p2 ∨ p5)))) → False) → False) := by
  intro assump_5
  have assump_29 : ((((p0 ∧ p0) → False) ∧ ((p3 → False) ∨ (p2 → False))) → (((p6 ∧ p0) ∨ (False → False)) ∨ ((p4 → False) ∧ (p2 ∨ p5)))) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        apply Or.inl
        apply Or.inr
        intro assump_18
        apply False.elim assump_18
      case inr assump_15 =>
        apply Or.inl
        apply Or.inr
        intro assump_23
        apply False.elim assump_23
  let assump_8 := assump_5 assump_29
  apply False.elim assump_8


variable (p4 p2 p7 p5 : Prop)
theorem file27_134905 : (((((True → False) ∨ (False ∧ p7)) ∧ ((p4 → p7) ∨ (p5 → p5))) ∧ (((p4 → False) ∨ (False ∨ p2)) ∨ ((p2 ∨ p2) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_3
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              have assump_108 : True := by
                apply True.intro
              let assump_22 := assump_6 assump_108
              apply False.elim assump_22
            case inr assump_17 =>
              cases assump_17
              case inl assump_26 =>
                apply False.elim assump_26
              case inr assump_27 =>
                have assump_109 : True := by
                  apply True.intro
                let assump_34 := assump_6 assump_109
                apply False.elim assump_34
          case inr assump_15 =>
            cases assump_15
            case intro assump_38 assump_39 =>
              cases assump_38
              case inl assump_40 =>
                have assump_110 : True := by
                  apply True.intro
                let assump_46 := assump_39 assump_110
                apply False.elim assump_46
              case inr assump_41 =>
                have assump_111 : True := by
                  apply True.intro
                let assump_54 := assump_39 assump_111
                apply False.elim assump_54
        case inr assump_11 =>
          cases assump_3
          case inl assump_60 =>
            cases assump_60
            case inl assump_62 =>
              have assump_112 : True := by
                apply True.intro
              let assump_68 := assump_6 assump_112
              apply False.elim assump_68
            case inr assump_63 =>
              cases assump_63
              case inl assump_72 =>
                apply False.elim assump_72
              case inr assump_73 =>
                have assump_113 : True := by
                  apply True.intro
                let assump_80 := assump_6 assump_113
                apply False.elim assump_80
          case inr assump_61 =>
            cases assump_61
            case intro assump_84 assump_85 =>
              cases assump_84
              case inl assump_86 =>
                have assump_114 : True := by
                  apply True.intro
                let assump_92 := assump_85 assump_114
                apply False.elim assump_92
              case inr assump_87 =>
                have assump_115 : True := by
                  apply True.intro
                let assump_100 := assump_85 assump_115
                apply False.elim assump_100
      case inr assump_7 =>
        cases assump_7
        case intro assump_104 assump_105 =>
          apply False.elim assump_104


variable (p3 p2 p1 p6 p7 p0 p5 p4 : Prop)
theorem file27_137910 : ((((((p1 → False) ∨ (p7 → False)) → ((p1 → False) → (p0 ∨ p0))) ∧ (((p3 → True) ∨ (p6 ∧ p0)) → False)) ∧ ((((p4 → True) ∧ (p4 ∨ p5)) → False) ∨ (((p6 → True) ∨ (p2 → False)) → ((p7 ∧ p7) ∧ (p2 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_35 : ((p3 → True) ∨ (p6 ∧ p0)) := by
          apply Or.inl
          intro assump_17
          apply True.intro
        let assump_16 := assump_5 assump_35
        apply False.elim assump_16
      case inr assump_11 =>
        have assump_36 : ((p3 → True) ∨ (p6 ∧ p0)) := by
          apply Or.inl
          intro assump_31
          apply True.intro
        let assump_30 := assump_5 assump_36
        apply False.elim assump_30


variable (p3 p7 p5 p6 p4 : Prop)
theorem file27_138812 : ((((((p5 → p6) ∧ (p6 → False)) → False) → (((p4 ∧ p6) ∨ (p4 → p3)) → ((p7 ∨ True) → (True ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_45 : ((((p5 → p6) ∧ (p6 → False)) → False) → (((p4 ∧ p6) ∨ (p4 → p3)) → ((p7 ∨ True) → (True ∨ p3)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_6
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply Or.inl
          apply True.intro
      case inr assump_13 =>
        apply Or.inl
        apply True.intro
    case inr assump_9 =>
      cases assump_6
      case inl assump_28 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          apply Or.inl
          apply True.intro
      case inr assump_29 =>
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


