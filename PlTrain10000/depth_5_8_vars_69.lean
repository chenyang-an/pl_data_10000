variable (p0 p2 p3 p6 p7 p1 : Prop)
theorem file69_44 : ((((((p1 ∧ False) ∧ (p6 ∨ p0)) ∨ ((p2 ∧ p7) → (False ∧ p0))) ∨ (((p1 ∧ p1) ∨ (False → p1)) ∧ ((p3 ∨ p2) ∨ (p1 → True)))) ∧ ((((p0 → False) → (True → p1)) ∧ ((p2 → p2) → False)) ∧ (((True → False) ∨ (p3 ∨ p1)) ∧ ((p6 → p1) ∧ (p6 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            apply False.elim assump_11
      case inr assump_7 =>
        cases assump_3
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_19
            case intro assump_26 assump_27 =>
              cases assump_26
              case inl assump_28 =>
                cases assump_27
                case intro assump_32 assump_33 =>
                  have assump_498 : True := by
                    apply True.intro
                  let assump_40 := assump_28 assump_498
                  apply False.elim assump_40
              case inr assump_29 =>
                cases assump_29
                case inl assump_44 =>
                  cases assump_27
                  case intro assump_48 assump_49 =>
                    have assump_499 : (p2 → p2) := by
                      intro assump_58
                      exact assump_58
                    let assump_57 := assump_21 assump_499
                    apply False.elim assump_57
                case inr assump_45 =>
                  cases assump_27
                  case intro assump_66 assump_67 =>
                    have assump_500 : (p2 → p2) := by
                      intro assump_76
                      exact assump_76
                    let assump_75 := assump_21 assump_500
                    apply False.elim assump_75
    case inr assump_5 =>
      cases assump_5
      case intro assump_82 assump_83 =>
        cases assump_82
        case inl assump_84 =>
          cases assump_84
          case intro assump_86 assump_87 =>
            cases assump_83
            case inl assump_92 =>
              cases assump_92
              case inl assump_94 =>
                cases assump_3
                case intro assump_98 assump_99 =>
                  cases assump_98
                  case intro assump_100 assump_101 =>
                    cases assump_99
                    case intro assump_106 assump_107 =>
                      cases assump_106
                      case inl assump_108 =>
                        cases assump_107
                        case intro assump_112 assump_113 =>
                          have assump_501 : True := by
                            apply True.intro
                          let assump_120 := assump_108 assump_501
                          apply False.elim assump_120
                      case inr assump_109 =>
                        cases assump_109
                        case inl assump_124 =>
                          cases assump_107
                          case intro assump_128 assump_129 =>
                            have assump_502 : (p2 → p2) := by
                              intro assump_138
                              exact assump_138
                            let assump_137 := assump_101 assump_502
                            apply False.elim assump_137
                        case inr assump_125 =>
                          cases assump_107
                          case intro assump_146 assump_147 =>
                            have assump_503 : (p2 → p2) := by
                              intro assump_156
                              exact assump_156
                            let assump_155 := assump_101 assump_503
                            apply False.elim assump_155
              case inr assump_95 =>
                cases assump_3
                case intro assump_164 assump_165 =>
                  cases assump_164
                  case intro assump_166 assump_167 =>
                    cases assump_165
                    case intro assump_172 assump_173 =>
                      cases assump_172
                      case inl assump_174 =>
                        cases assump_173
                        case intro assump_178 assump_179 =>
                          have assump_504 : True := by
                            apply True.intro
                          let assump_186 := assump_174 assump_504
                          apply False.elim assump_186
                      case inr assump_175 =>
                        cases assump_175
                        case inl assump_190 =>
                          cases assump_173
                          case intro assump_194 assump_195 =>
                            have assump_505 : (p2 → p2) := by
                              intro assump_204
                              exact assump_204
                            let assump_203 := assump_167 assump_505
                            apply False.elim assump_203
                        case inr assump_191 =>
                          cases assump_173
                          case intro assump_212 assump_213 =>
                            have assump_506 : (p2 → p2) := by
                              intro assump_222
                              exact assump_222
                            let assump_221 := assump_167 assump_506
                            apply False.elim assump_221
            case inr assump_93 =>
              cases assump_3
              case intro assump_230 assump_231 =>
                cases assump_230
                case intro assump_232 assump_233 =>
                  cases assump_231
                  case intro assump_238 assump_239 =>
                    cases assump_238
                    case inl assump_240 =>
                      cases assump_239
                      case intro assump_244 assump_245 =>
                        have assump_507 : True := by
                          apply True.intro
                        let assump_252 := assump_240 assump_507
                        apply False.elim assump_252
                    case inr assump_241 =>
                      cases assump_241
                      case inl assump_256 =>
                        cases assump_239
                        case intro assump_260 assump_261 =>
                          have assump_508 : (p2 → p2) := by
                            intro assump_270
                            exact assump_270
                          let assump_269 := assump_233 assump_508
                          apply False.elim assump_269
                      case inr assump_257 =>
                        cases assump_239
                        case intro assump_278 assump_279 =>
                          have assump_509 : (p2 → p2) := by
                            intro assump_288
                            exact assump_288
                          let assump_287 := assump_233 assump_509
                          apply False.elim assump_287
        case inr assump_85 =>
          cases assump_83
          case inl assump_296 =>
            cases assump_296
            case inl assump_298 =>
              cases assump_3
              case intro assump_302 assump_303 =>
                cases assump_302
                case intro assump_304 assump_305 =>
                  cases assump_303
                  case intro assump_310 assump_311 =>
                    cases assump_310
                    case inl assump_312 =>
                      cases assump_311
                      case intro assump_316 assump_317 =>
                        have assump_510 : True := by
                          apply True.intro
                        let assump_324 := assump_312 assump_510
                        apply False.elim assump_324
                    case inr assump_313 =>
                      cases assump_313
                      case inl assump_328 =>
                        cases assump_311
                        case intro assump_332 assump_333 =>
                          have assump_511 : (p2 → p2) := by
                            intro assump_342
                            exact assump_342
                          let assump_341 := assump_305 assump_511
                          apply False.elim assump_341
                      case inr assump_329 =>
                        cases assump_311
                        case intro assump_350 assump_351 =>
                          have assump_512 : (p2 → p2) := by
                            intro assump_360
                            exact assump_360
                          let assump_359 := assump_305 assump_512
                          apply False.elim assump_359
            case inr assump_299 =>
              cases assump_3
              case intro assump_368 assump_369 =>
                cases assump_368
                case intro assump_370 assump_371 =>
                  cases assump_369
                  case intro assump_376 assump_377 =>
                    cases assump_376
                    case inl assump_378 =>
                      cases assump_377
                      case intro assump_382 assump_383 =>
                        have assump_513 : True := by
                          apply True.intro
                        let assump_390 := assump_378 assump_513
                        apply False.elim assump_390
                    case inr assump_379 =>
                      cases assump_379
                      case inl assump_394 =>
                        cases assump_377
                        case intro assump_398 assump_399 =>
                          have assump_514 : (p2 → p2) := by
                            intro assump_408
                            exact assump_408
                          let assump_407 := assump_371 assump_514
                          apply False.elim assump_407
                      case inr assump_395 =>
                        cases assump_377
                        case intro assump_416 assump_417 =>
                          have assump_515 : (p2 → p2) := by
                            intro assump_426
                            exact assump_426
                          let assump_425 := assump_371 assump_515
                          apply False.elim assump_425
          case inr assump_297 =>
            cases assump_3
            case intro assump_434 assump_435 =>
              cases assump_434
              case intro assump_436 assump_437 =>
                cases assump_435
                case intro assump_442 assump_443 =>
                  cases assump_442
                  case inl assump_444 =>
                    cases assump_443
                    case intro assump_448 assump_449 =>
                      have assump_516 : True := by
                        apply True.intro
                      let assump_456 := assump_444 assump_516
                      apply False.elim assump_456
                  case inr assump_445 =>
                    cases assump_445
                    case inl assump_460 =>
                      cases assump_443
                      case intro assump_464 assump_465 =>
                        have assump_517 : (p2 → p2) := by
                          intro assump_474
                          exact assump_474
                        let assump_473 := assump_437 assump_517
                        apply False.elim assump_473
                    case inr assump_461 =>
                      cases assump_443
                      case intro assump_482 assump_483 =>
                        have assump_518 : (p2 → p2) := by
                          intro assump_492
                          exact assump_492
                        let assump_491 := assump_437 assump_518
                        apply False.elim assump_491


variable (p0 p5 : Prop)
theorem file69_12056 : (((((True → False) → False) ∨ ((p0 → False) ∨ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → False) ∨ ((p0 → False) ∨ (p5 → False))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p0 p3 p4 p2 p6 p1 p5 : Prop)
theorem file69_12533 : (((((p7 → True) ∨ (p6 → False)) → False) → False) ∨ ((((p1 → False) ∨ (p1 ∨ p2)) → ((p7 → p0) → (p0 → p7))) → (((p5 ∧ True) → (p2 ∧ p1)) ∨ ((p6 → p4) → (p3 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p7 → True) ∨ (p6 → False)) := by
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p5 p0 p3 p7 p1 p6 : Prop)
theorem file69_12974 : ((((((True ∨ p5) → False) ∨ ((p0 → p1) → (p1 → False))) → False) ∧ ((((p7 → False) → False) ∧ ((p1 → False) → False)) ∧ (((p1 → p0) ∧ (p6 ∧ False)) ∧ ((p7 → True) → (p3 → p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              apply False.elim assump_21


variable (p6 p0 p2 p5 p3 : Prop)
theorem file69_13657 : (((((p3 ∧ False) ∧ (p0 → False)) ∧ ((p5 ∨ False) → False)) ∧ (((p2 → p0) ∨ (False → p3)) → ((p0 → p3) → False))) → ((((True ∨ p0) ∧ (p6 → False)) → False) ∨ (((p6 ∧ True) ∨ (p2 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9


variable (p6 p4 : Prop)
theorem file69_14190 : (((((p6 ∧ True) → False) → ((p6 ∧ p4) → (True → False))) → False) → False) := by
  intro assump_4
  have assump_28 : (((p6 ∧ True) → False) → ((p6 ∧ p4) → (True → False))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      have assump_29 : (p6 ∧ True) := by
        apply And.intro
        exact assump_13
        apply True.intro
      let assump_21 := assump_8 assump_29
      apply False.elim assump_21
  let assump_7 := assump_4 assump_28
  apply False.elim assump_7


variable (p6 p4 p1 p5 p2 : Prop)
theorem file69_14794 : (((((p6 → p2) ∧ (p1 ∧ p2)) ∧ ((p4 → True) → (p5 ∨ True))) ∧ (((p2 → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          have assump_31 : ((p2 → False) → False) := by
            intro assump_21
            have assump_32 : p2 := by
              exact assump_11
            let assump_24 := assump_21 assump_32
            apply False.elim assump_24
          let assump_20 := assump_3 assump_31
          apply False.elim assump_20


variable (p4 p1 p0 p3 p7 p5 : Prop)
theorem file69_15533 : ((((((p1 ∨ p3) → False) → ((p1 → False) → False)) ∧ (((p3 ∨ p4) → False) → ((p3 → p3) ∨ (p4 ∨ p1)))) ∧ ((((False → False) ∧ (True ∧ p4)) ∧ ((p5 → True) → (p1 ∧ p0))) ∧ (((p3 ∨ True) → False) ∧ ((p7 ∧ p4) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_11
              case intro assump_26 assump_27 =>
                have assump_37 : (p3 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_33 := assump_26 assump_37
                apply False.elim assump_33


variable (p0 p1 p2 p4 p6 : Prop)
theorem file69_16506 : ((((((True ∨ p0) ∨ (p0 → False)) → False) → (((True ∧ p2) ∧ (p1 ∧ True)) ∧ ((p6 → p0) ∧ (p0 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_42 : ((((True ∨ p0) ∨ (p0 → False)) → False) → (((True ∧ p2) ∧ (p1 ∧ True)) ∧ ((p6 → p0) ∧ (p0 ∧ p4)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    apply True.intro
    have assump_43 : ((True ∨ p0) ∨ (p0 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_43
    apply False.elim assump_8
    apply And.intro
    have assump_44 : ((True ∨ p0) ∨ (p0 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_14 := assump_5 assump_44
    apply False.elim assump_14
    apply True.intro
    apply And.intro
    intro assump_18
    have assump_45 : ((True ∨ p0) ∨ (p0 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_23 := assump_5 assump_45
    apply False.elim assump_23
    apply And.intro
    have assump_46 : ((True ∨ p0) ∨ (p0 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_29 := assump_5 assump_46
    apply False.elim assump_29
    have assump_47 : ((True ∨ p0) ∨ (p0 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_35 := assump_5 assump_47
    apply False.elim assump_35
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p3 p7 p4 p1 p5 p2 p6 p0 : Prop)
theorem file69_18042 : (((((p3 ∧ True) ∨ (p2 ∧ p2)) ∧ ((p0 ∧ p4) ∨ (p3 → False))) → (((p0 → False) ∧ (p3 → False)) ∧ ((p6 → p7) → (p0 → False)))) → ((((True → False) ∧ (p7 → p1)) → ((False → True) ∧ (p5 → False))) ∨ (((p0 ∨ p0) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  apply True.intro
  intro assump_6
  cases assump_4
  case intro assump_9 assump_10 =>
    have assump_20 : True := by
      apply True.intro
    let assump_16 := assump_9 assump_20
    apply False.elim assump_16


variable (p1 p7 p6 p0 : Prop)
theorem file69_18625 : ((((((False ∧ p1) → False) → False) → False) → ((((p0 ∧ True) ∧ (True ∨ True)) ∨ ((p7 ∧ True) ∨ (p0 → p6))) → False)) → False) := by
  intro assump_1
  have assump_42 : ((((False ∧ p1) → False) → False) → False) := by
    intro assump_5
    have assump_43 : ((False ∧ p1) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_43
    apply False.elim assump_8
  let assump_4 := assump_1 assump_42
  have assump_44 : (((p0 ∧ True) ∧ (True ∨ True)) ∨ ((p7 ∧ True) ∨ (p0 → p6))) := by
    apply Or.inr
    apply Or.inr
    intro assump_18
    have assump_45 : ((((False ∧ p1) → False) → False) → False) := by
      intro assump_23
      have assump_46 : ((False ∧ p1) → False) := by
        intro assump_27
        cases assump_27
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
      let assump_26 := assump_23 assump_46
      apply False.elim assump_26
    let assump_22 := assump_1 assump_45
    have assump_47 : (((p0 ∧ True) ∧ (True ∨ True)) ∨ ((p7 ∧ True) ∨ (p0 → p6))) := by
      apply Or.inl
      apply And.intro
      apply And.intro
      exact assump_18
      apply True.intro
      apply Or.inl
      apply True.intro
    let assump_35 := assump_22 assump_47
    apply False.elim assump_35
  let assump_17 := assump_4 assump_44
  apply False.elim assump_17


variable (p5 p7 p4 : Prop)
theorem file69_20088 : (((((p7 → False) → False) → False) ∧ (((p4 → False) ∧ (p7 → p7)) ∧ ((p5 → p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_23 : (p5 → p5) := by
          intro assump_17
          exact assump_17
        let assump_16 := assump_7 assump_23
        apply False.elim assump_16


variable (p7 p6 p4 p0 p5 p2 : Prop)
theorem file69_20606 : ((((((p5 ∧ p6) → (p4 → p2)) ∨ ((p5 → True) ∧ (p0 → False))) → (((False ∧ p2) → (p4 → False)) → ((p7 ∨ p4) ∨ (True ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 ∧ p6) → (p4 → p2)) ∨ ((p5 → True) ∧ (p0 → False))) → (((False ∧ p2) → (p4 → False)) → ((p7 ∨ p4) ∨ (True ∧ True)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    case inr assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply Or.inr
        apply And.intro
        apply True.intro
        apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p3 p1 p6 p2 p4 p5 : Prop)
theorem file69_21400 : ((((((p1 ∧ p5) → False) ∧ ((p0 → False) → (p0 → False))) ∧ (((p1 → p0) ∧ (p5 → p4)) → ((p4 → p6) → False))) ∧ ((((p1 ∨ False) ∨ (p4 ∧ p6)) ∧ ((False ∧ p3) ∧ (False → False))) ∧ (((p3 → False) ∨ (p2 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_26
              case inr assump_21 =>
                apply False.elim assump_21
            case inr assump_19 =>
              cases assump_19
              case intro assump_32 assump_33 =>
                cases assump_17
                case intro assump_38 assump_39 =>
                  cases assump_38
                  case intro assump_40 assump_41 =>
                    apply False.elim assump_40


variable (p4 p0 p7 p3 p6 : Prop)
theorem file69_22757 : (((((p3 ∧ False) ∨ (True → False)) ∧ ((False ∨ p0) ∧ (True → p3))) → False) ∨ ((((p6 → False) → (p4 → False)) ∧ ((p0 ∨ p3) → (p7 → p4))) ∨ (((p6 ∧ False) → (p0 ∨ True)) ∧ ((p7 ∧ True) → (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7
    case inr assump_5 =>
      cases assump_3
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          apply False.elim assump_16
        case inr assump_17 =>
          have assump_31 : True := by
            apply True.intro
          let assump_27 := assump_5 assump_31
          apply False.elim assump_27


variable (p0 p4 p7 p1 : Prop)
theorem file69_23597 : ((((((p7 → False) → (True ∨ p0)) → False) → (((p4 ∨ p4) ∨ (p1 ∨ p4)) ∧ ((p0 → p1) ∧ (False ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p7 → False) → (True ∨ p0)) → False) → (((p4 ∨ p4) ∨ (p1 ∨ p4)) ∧ ((p0 → p1) ∧ (False ∨ p4)))) := by
    intro assump_5
    apply And.intro
    have assump_40 : ((p7 → False) → (True ∨ p0)) := by
      intro assump_9
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_40
    apply False.elim assump_8
    apply And.intro
    intro assump_15
    have assump_41 : ((p7 → False) → (True ∨ p0)) := by
      intro assump_21
      apply Or.inl
      apply True.intro
    let assump_20 := assump_5 assump_41
    apply False.elim assump_20
    have assump_42 : ((p7 → False) → (True ∨ p0)) := by
      intro assump_30
      apply Or.inl
      apply True.intro
    let assump_29 := assump_5 assump_42
    apply False.elim assump_29
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p5 p0 p7 p3 p4 p2 p1 p6 : Prop)
theorem file69_24641 : (((((p2 → True) ∧ (p7 ∧ p7)) ∨ ((p3 → False) → (p7 → False))) → False) → ((((p2 ∧ p0) ∨ (p4 ∧ p0)) ∨ ((p6 ∨ p1) ∧ (False → False))) ∧ (((p7 ∨ p5) → (False ∧ False)) → False))) := by
  intro assump_1
  apply And.intro
  have assump_45 : (((p2 → True) ∧ (p7 ∧ p7)) ∨ ((p3 → False) → (p7 → False))) := by
    apply Or.inr
    intro assump_6
    intro assump_7
    have assump_46 : (((p2 → True) ∧ (p7 ∧ p7)) ∨ ((p3 → False) → (p7 → False))) := by
      apply Or.inl
      apply And.intro
      intro assump_15
      apply True.intro
      apply And.intro
      exact assump_7
      exact assump_7
    let assump_14 := assump_1 assump_46
    apply False.elim assump_14
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4
  intro assump_22
  have assump_47 : (((p2 → True) ∧ (p7 ∧ p7)) ∨ ((p3 → False) → (p7 → False))) := by
    apply Or.inr
    intro assump_29
    intro assump_30
    have assump_48 : (((p2 → True) ∧ (p7 ∧ p7)) ∨ ((p3 → False) → (p7 → False))) := by
      apply Or.inl
      apply And.intro
      intro assump_38
      apply True.intro
      apply And.intro
      exact assump_30
      exact assump_30
    let assump_37 := assump_1 assump_48
    apply False.elim assump_37
  let assump_27 := assump_1 assump_47
  apply False.elim assump_27


variable (p6 p0 p2 p5 p1 p7 : Prop)
theorem file69_25968 : ((((((p2 ∨ p7) ∨ (p7 ∧ p1)) ∨ ((p2 ∧ p0) → False)) → False) ∨ ((((p5 → p6) ∧ (p7 ∧ False)) → False) ∧ (((True → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_40 : (((p2 ∨ p7) ∨ (p7 ∧ p1)) ∨ ((p2 ∧ p0) → False)) := by
      apply Or.inr
      intro assump_7
      cases assump_7
      case intro assump_8 assump_9 =>
        have assump_41 : (((p2 ∨ p7) ∨ (p7 ∧ p1)) ∨ ((p2 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_8
        let assump_16 := assump_2 assump_41
        apply False.elim assump_16
    let assump_6 := assump_2 assump_40
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_23 assump_24 =>
      have assump_42 : ((True → False) → False) := by
        intro assump_30
        have assump_43 : True := by
          apply True.intro
        let assump_33 := assump_30 assump_43
        apply False.elim assump_33
      let assump_29 := assump_24 assump_42
      apply False.elim assump_29


variable (p2 p1 p6 p0 p3 p4 p5 : Prop)
theorem file69_27114 : (((((True → False) ∧ (p3 ∨ p3)) → False) ∨ (((p3 → True) → (True ∨ p4)) ∨ ((p3 ∨ True) ∨ (p2 ∧ p1)))) ∨ ((((False → False) → (p0 ∨ p6)) → ((p5 ∨ True) ∨ (p4 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_22 : True := by
        apply True.intro
      let assump_11 := assump_2 assump_22
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_23 : True := by
        apply True.intro
      let assump_18 := assump_2 assump_23
      apply False.elim assump_18


variable (p5 p7 p6 p4 p3 p1 p0 : Prop)
theorem file69_27796 : ((((((False ∧ p3) → False) ∧ ((p5 → False) ∧ (p4 → False))) ∨ (((p0 ∨ p1) → (p1 → False)) ∨ ((p7 → False) → (p6 ∧ p5)))) ∧ ((((False → p3) ∨ (p6 ∧ p6)) → ((p7 → False) → False)) ∧ (((True ∨ p5) → False) ∧ ((False → False) ∨ (True ∨ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              cases assump_21
              case inl assump_24 =>
                have assump_118 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_29 := assump_20 assump_118
                apply False.elim assump_29
              case inr assump_25 =>
                cases assump_25
                case inl assump_33 =>
                  have assump_119 : (True ∨ p5) := by
                    apply Or.inl
                    apply True.intro
                  let assump_37 := assump_20 assump_119
                  apply False.elim assump_37
                case inr assump_34 =>
                  have assump_120 : (True ∨ p5) := by
                    apply Or.inl
                    apply True.intro
                  let assump_44 := assump_20 assump_120
                  apply False.elim assump_44
    case inr assump_5 =>
      cases assump_5
      case inl assump_48 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          cases assump_53
          case intro assump_56 assump_57 =>
            cases assump_57
            case inl assump_60 =>
              have assump_121 : (True ∨ p5) := by
                apply Or.inl
                apply True.intro
              let assump_65 := assump_56 assump_121
              apply False.elim assump_65
            case inr assump_61 =>
              cases assump_61
              case inl assump_69 =>
                have assump_122 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_73 := assump_56 assump_122
                apply False.elim assump_73
              case inr assump_70 =>
                have assump_123 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_80 := assump_56 assump_123
                apply False.elim assump_80
      case inr assump_49 =>
        cases assump_3
        case intro assump_86 assump_87 =>
          cases assump_87
          case intro assump_90 assump_91 =>
            cases assump_91
            case inl assump_94 =>
              have assump_124 : (True ∨ p5) := by
                apply Or.inl
                apply True.intro
              let assump_99 := assump_90 assump_124
              apply False.elim assump_99
            case inr assump_95 =>
              cases assump_95
              case inl assump_103 =>
                have assump_125 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_107 := assump_90 assump_125
                apply False.elim assump_107
              case inr assump_104 =>
                have assump_126 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_114 := assump_90 assump_126
                apply False.elim assump_114


variable (p5 p6 p3 p2 p0 p4 p1 : Prop)
theorem file69_31412 : (((((p5 ∧ p6) ∧ (p1 ∧ False)) → False) → False) → ((((p3 → p3) → (False → p6)) → False) ∨ (((p2 → False) ∨ (p3 ∧ p5)) ∨ ((p2 ∧ p5) ∨ (p0 → p4))))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  have assump_35 : (((p5 ∧ p6) ∧ (p1 ∧ False)) → False) := by
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_19
        case intro assump_26 assump_27 =>
          apply False.elim assump_27
  let assump_16 := assump_5 assump_35
  apply False.elim assump_16


variable (p0 p5 p1 p6 : Prop)
theorem file69_32040 : (((((False → False) ∨ (True ∧ p5)) ∨ ((p6 → p1) ∧ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → False) ∨ (True ∧ p5)) ∨ ((p6 → p1) ∧ (p0 → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p0 p3 p5 p6 p7 : Prop)
theorem file69_32442 : (((((p7 → False) ∨ (p6 → p7)) ∨ ((p0 ∨ False) → (p3 ∨ p6))) ∧ (((p5 ∨ p3) → (p6 → False)) ∧ ((p7 → p2) ∧ (p5 ∧ False)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              apply False.elim assump_23
      case inr assump_11 =>
        cases assump_7
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            cases assump_35
            case intro assump_38 assump_39 =>
              apply False.elim assump_39
    case inr assump_9 =>
      cases assump_7
      case intro assump_46 assump_47 =>
        cases assump_47
        case intro assump_50 assump_51 =>
          cases assump_51
          case intro assump_54 assump_55 =>
            apply False.elim assump_55


variable (p4 p1 p7 p2 p3 p5 : Prop)
theorem file69_33588 : (((((True ∧ False) ∨ (p7 → False)) → ((False → False) ∨ (p5 ∨ p3))) ∨ (((True ∧ p3) ∧ (p4 ∧ p4)) → False)) ∨ ((((p5 → False) ∧ (p7 ∨ p1)) → ((p3 ∧ p1) ∨ (p5 ∨ p2))) ∧ (((p5 ∨ False) → False) ∨ ((p7 ∧ p2) ∧ (p1 ∧ False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5
  case inr assump_3 =>
    apply Or.inl
    intro assump_12
    apply False.elim assump_12


variable (p1 p4 p6 p5 p0 p7 p2 : Prop)
theorem file69_34145 : (((((p2 ∧ p4) → False) → False) ∧ (((False → p2) ∨ (p6 → p4)) → False)) → ((((p2 → p0) → (p5 ∨ p2)) ∧ ((p7 ∧ p0) ∧ (True → False))) ∧ (((p6 ∧ False) ∧ (p0 ∧ p5)) → ((p7 ∨ p4) ∨ (p1 ∨ p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_69 : ((False → p2) ∨ (p6 → p4)) := by
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_6 assump_69
    apply False.elim assump_11
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_18 assump_19 =>
    have assump_70 : ((False → p2) ∨ (p6 → p4)) := by
      apply Or.inl
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_19 assump_70
    apply False.elim assump_24
  cases assump_1
  case intro assump_31 assump_32 =>
    have assump_71 : ((False → p2) ∨ (p6 → p4)) := by
      apply Or.inl
      intro assump_38
      apply False.elim assump_38
    let assump_37 := assump_32 assump_71
    apply False.elim assump_37
  intro assump_44
  cases assump_1
  case intro assump_47 assump_48 =>
    have assump_72 : ((False → p2) ∨ (p6 → p4)) := by
      apply Or.inl
      intro assump_54
      apply False.elim assump_54
    let assump_53 := assump_48 assump_72
    apply False.elim assump_53
  intro assump_60
  cases assump_60
  case intro assump_61 assump_62 =>
    cases assump_61
    case intro assump_63 assump_64 =>
      apply False.elim assump_64


variable (p0 p6 p7 p2 : Prop)
theorem file69_35692 : ((((((p7 → p7) ∨ (p2 → False)) ∨ ((True ∨ True) → False)) ∨ (((p0 ∨ p6) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p7 → p7) ∨ (p2 → False)) ∨ ((True ∨ True) → False)) ∨ (((p0 ∨ p6) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p0 p7 p6 p2 p4 p5 : Prop)
theorem file69_36155 : ((((((p0 ∧ p6) → (p0 → False)) → False) → (((p7 → p2) ∧ (p6 ∧ p7)) → ((p0 → p1) → (True ∨ p4)))) → ((((False → p7) → False) ∧ ((False → False) ∧ (p5 ∧ p7))) ∧ (((p2 → p0) → (True ∧ p6)) ∨ ((p0 ∧ p6) ∨ (p2 → p4))))) → False) := by
  intro assump_1
  have assump_31 : ((((p0 ∧ p6) → (p0 → False)) → False) → (((p7 → p2) ∧ (p6 ∧ p7)) → ((p0 → p1) → (True ∨ p4)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_31
  let assump_22 := And.left assump_4
  let assump_23 := And.left assump_22
  have assump_32 : (False → p7) := by
    intro assump_25
    apply False.elim assump_25
  let assump_24 := assump_23 assump_32
  apply False.elim assump_24


variable (p3 p2 p0 p4 p1 p6 : Prop)
theorem file69_37073 : ((((((p3 → p6) → False) → ((p2 → p4) ∨ (False ∨ p1))) ∨ (((p4 ∨ p0) → (True → False)) → ((p3 → False) ∧ (p3 → False)))) ∧ ((((p6 → False) → False) ∧ ((p1 ∧ False) ∧ (p3 ∧ p2))) ∧ (((p3 → p2) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
    case inr assump_5 =>
      cases assump_3
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_27
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              apply False.elim assump_33


variable (p0 p7 p3 p4 p1 p2 p5 : Prop)
theorem file69_38120 : (((((p5 ∧ p7) → False) → ((p4 → p3) ∧ (p7 → False))) → False) → ((((p4 ∨ p7) → False) → ((p1 ∧ p2) ∧ (p2 ∧ True))) ∨ (((p2 → False) → (True → p4)) → ((p0 ∧ False) → (p1 → p5))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  apply And.intro
  have assump_95 : (((p5 ∧ p7) → False) → ((p4 → p3) ∧ (p7 → False))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    have assump_96 : (p4 ∨ p7) := by
      apply Or.inl
      exact assump_10
    let assump_17 := assump_4 assump_96
    apply False.elim assump_17
    intro assump_21
    have assump_97 : (p4 ∨ p7) := by
      apply Or.inr
      exact assump_21
    let assump_28 := assump_4 assump_97
    apply False.elim assump_28
  let assump_8 := assump_1 assump_95
  apply False.elim assump_8
  have assump_98 : (((p5 ∧ p7) → False) → ((p4 → p3) ∧ (p7 → False))) := by
    intro assump_39
    apply And.intro
    intro assump_40
    have assump_99 : (p4 ∨ p7) := by
      apply Or.inl
      exact assump_40
    let assump_47 := assump_4 assump_99
    apply False.elim assump_47
    intro assump_51
    have assump_100 : (p4 ∨ p7) := by
      apply Or.inr
      exact assump_51
    let assump_58 := assump_4 assump_100
    apply False.elim assump_58
  let assump_38 := assump_1 assump_98
  apply False.elim assump_38
  apply And.intro
  have assump_101 : (((p5 ∧ p7) → False) → ((p4 → p3) ∧ (p7 → False))) := by
    intro assump_69
    apply And.intro
    intro assump_70
    have assump_102 : (p4 ∨ p7) := by
      apply Or.inl
      exact assump_70
    let assump_77 := assump_4 assump_102
    apply False.elim assump_77
    intro assump_81
    have assump_103 : (p4 ∨ p7) := by
      apply Or.inr
      exact assump_81
    let assump_88 := assump_4 assump_103
    apply False.elim assump_88
  let assump_68 := assump_1 assump_101
  apply False.elim assump_68
  apply True.intro


variable (p0 p7 p4 p5 p1 p6 p2 : Prop)
theorem file69_40058 : (((((p6 → False) → False) ∨ ((p2 → p2) → False)) ∨ (((p4 → False) ∨ (False → False)) ∧ ((p2 ∧ p0) ∧ (p7 → False)))) → ((((p2 → p4) ∨ (p6 ∨ p5)) → ((p0 → p0) → (True ∨ p1))) ∨ (((p2 → False) → False) → ((False → p7) ∧ (p2 → p6))))) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      apply Or.inl
      intro assump_12
      intro assump_13
      cases assump_12
      case inl assump_16 =>
        apply Or.inl
        apply True.intro
      case inr assump_17 =>
        cases assump_17
        case inl assump_20 =>
          apply Or.inl
          apply True.intro
        case inr assump_21 =>
          apply Or.inl
          apply True.intro
    case inr assump_9 =>
      apply Or.inl
      intro assump_28
      intro assump_29
      cases assump_28
      case inl assump_32 =>
        apply Or.inl
        apply True.intro
      case inr assump_33 =>
        cases assump_33
        case inl assump_36 =>
          apply Or.inl
          apply True.intro
        case inr assump_37 =>
          apply Or.inl
          apply True.intro
  case inr assump_7 =>
    cases assump_7
    case intro assump_42 assump_43 =>
      cases assump_42
      case inl assump_44 =>
        cases assump_43
        case intro assump_48 assump_49 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            apply Or.inl
            intro assump_58
            intro assump_59
            cases assump_58
            case inl assump_62 =>
              apply Or.inl
              apply True.intro
            case inr assump_63 =>
              cases assump_63
              case inl assump_66 =>
                apply Or.inl
                apply True.intro
              case inr assump_67 =>
                apply Or.inl
                apply True.intro
      case inr assump_45 =>
        cases assump_43
        case intro assump_74 assump_75 =>
          cases assump_74
          case intro assump_76 assump_77 =>
            apply Or.inl
            intro assump_84
            intro assump_85
            cases assump_84
            case inl assump_88 =>
              apply Or.inl
              apply True.intro
            case inr assump_89 =>
              cases assump_89
              case inl assump_92 =>
                apply Or.inl
                apply True.intro
              case inr assump_93 =>
                apply Or.inl
                apply True.intro


variable (p5 p1 p2 p0 p6 : Prop)
theorem file69_42572 : (((((False ∨ True) → False) → ((p2 ∧ p0) → (p6 ∨ p6))) → False) → ((((False ∧ p1) ∧ (p0 ∨ True)) ∧ ((p6 → False) → (p5 ∨ p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p2 p0 p6 p5 p7 p3 p1 : Prop)
theorem file69_43011 : ((((((False → p3) → False) → False) → False) ∨ ((((False ∧ p1) ∧ (p2 → False)) ∧ ((p7 → p6) → (p5 → False))) ∧ (((p2 ∧ p2) ∧ (p0 ∨ p3)) ∨ ((p0 → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_30 : (((False → p3) → False) → False) := by
      intro assump_7
      have assump_31 : (False → p3) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_7 assump_31
      apply False.elim assump_10
    let assump_6 := assump_2 assump_30
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            apply False.elim assump_26


variable (p5 p7 p2 p6 p3 p4 p0 : Prop)
theorem file69_43953 : ((((((p6 → False) → False) ∧ ((p2 ∨ p5) ∧ (p4 ∨ p4))) → (((p3 ∧ p5) → False) → ((p5 ∨ p5) → False))) ∧ ((((p4 ∨ True) ∨ (p7 → p4)) → False) ∧ (((p2 → True) ∨ (p5 → p2)) ∧ ((True ∨ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_30 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_18 := assump_11 assump_30
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_31 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_26 := assump_11 assump_31
          apply False.elim assump_26


variable (p3 p2 p7 p4 : Prop)
theorem file69_44852 : ((((((False → False) ∧ (p2 → p2)) ∨ ((p3 ∨ p2) → False)) ∨ (((p7 → False) → (p4 ∨ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((False → False) ∧ (p2 → p2)) ∨ ((p3 ∨ p2) → False)) ∨ (((p7 → False) → (p4 ∨ p7)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p5 p6 p0 : Prop)
theorem file69_45370 : ((((((p0 ∧ p5) ∧ (p2 ∧ p5)) ∧ ((p5 → False) ∧ (p6 ∧ p0))) → False) → False) → False) := by
  intro assump_19
  have assump_59 : ((((p0 ∧ p5) ∧ (p2 ∧ p5)) ∧ ((p5 → False) ∧ (p6 ∧ p0))) → False) := by
    intro assump_23
    cases assump_23
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_27
          case intro assump_34 assump_35 =>
            cases assump_25
            case intro assump_40 assump_41 =>
              cases assump_41
              case intro assump_44 assump_45 =>
                have assump_60 : p5 := by
                  exact assump_35
                let assump_52 := assump_40 assump_60
                apply False.elim assump_52
  let assump_22 := assump_19 assump_59
  apply False.elim assump_22


variable (p4 p1 p3 : Prop)
theorem file69_46288 : (((((p4 ∨ True) ∨ (p3 → False)) ∧ ((True ∧ p1) ∨ (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p4 ∨ True) ∨ (p3 → False)) ∧ ((True ∧ p1) ∨ (p1 → False))) := by
    apply And.intro
    apply Or.inl
    apply Or.inr
    apply True.intro
    apply Or.inr
    intro assump_5
    have assump_17 : (((p4 ∨ True) ∨ (p3 → False)) ∧ ((True ∧ p1) ∨ (p1 → False))) := by
      apply And.intro
      apply Or.inl
      apply Or.inr
      apply True.intro
      apply Or.inl
      apply And.intro
      apply True.intro
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p0 p2 p6 p4 p1 : Prop)
theorem file69_47042 : (((((p6 → False) → (True → False)) ∧ ((p6 ∧ True) → False)) → (((p4 → False) ∧ (p0 → False)) ∨ ((p5 ∧ p1) ∧ (p2 → False)))) ∨ ((((False ∨ False) ∧ (p1 → p1)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_8
    have assump_46 : (p6 → False) := by
      intro assump_14
      have assump_47 : (p6 ∧ True) := by
        apply And.intro
        exact assump_14
        apply True.intro
      let assump_19 := assump_3 assump_47
      apply False.elim assump_19
    let assump_13 := assump_2 assump_46
    have assump_48 : True := by
      apply True.intro
    let assump_23 := assump_13 assump_48
    apply False.elim assump_23
    intro assump_27
    have assump_49 : (p6 → False) := by
      intro assump_33
      have assump_50 : (p6 ∧ True) := by
        apply And.intro
        exact assump_33
        apply True.intro
      let assump_38 := assump_3 assump_50
      apply False.elim assump_38
    let assump_32 := assump_2 assump_49
    have assump_51 : True := by
      apply True.intro
    let assump_42 := assump_32 assump_51
    apply False.elim assump_42


variable (p2 p4 p7 p1 p6 p5 p3 : Prop)
theorem file69_48283 : (((((p7 ∧ False) → (p6 → p7)) → False) ∧ (((p2 → p3) ∨ (p6 → False)) ∧ ((p1 ∧ True) ∨ (p3 ∨ p2)))) → ((((p6 ∨ True) → (p5 → False)) → False) ∧ (((False ∧ False) → (p1 → False)) → ((p4 → False) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case inl assump_15 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            have assump_285 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_26
              intro assump_27
              cases assump_26
              case intro assump_30 assump_31 =>
                apply False.elim assump_31
            let assump_25 := assump_5 assump_285
            apply False.elim assump_25
        case inr assump_16 =>
          cases assump_16
          case inl assump_39 =>
            have assump_286 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_46
              intro assump_47
              cases assump_46
              case intro assump_50 assump_51 =>
                apply False.elim assump_51
            let assump_45 := assump_5 assump_286
            apply False.elim assump_45
          case inr assump_40 =>
            have assump_287 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_65
              intro assump_66
              cases assump_65
              case intro assump_69 assump_70 =>
                apply False.elim assump_70
            let assump_64 := assump_5 assump_287
            apply False.elim assump_64
      case inr assump_12 =>
        cases assump_10
        case inl assump_80 =>
          cases assump_80
          case intro assump_82 assump_83 =>
            have assump_288 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_91
              intro assump_92
              cases assump_91
              case intro assump_95 assump_96 =>
                apply False.elim assump_96
            let assump_90 := assump_5 assump_288
            apply False.elim assump_90
        case inr assump_81 =>
          cases assump_81
          case inl assump_104 =>
            have assump_289 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_111
              intro assump_112
              cases assump_111
              case intro assump_115 assump_116 =>
                apply False.elim assump_116
            let assump_110 := assump_5 assump_289
            apply False.elim assump_110
          case inr assump_105 =>
            have assump_290 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_129
              intro assump_130
              cases assump_129
              case intro assump_133 assump_134 =>
                apply False.elim assump_134
            let assump_128 := assump_5 assump_290
            apply False.elim assump_128
  intro assump_142
  intro assump_143
  cases assump_1
  case intro assump_148 assump_149 =>
    cases assump_149
    case intro assump_152 assump_153 =>
      cases assump_152
      case inl assump_154 =>
        cases assump_153
        case inl assump_158 =>
          cases assump_158
          case intro assump_160 assump_161 =>
            have assump_291 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_169
              intro assump_170
              cases assump_169
              case intro assump_173 assump_174 =>
                apply False.elim assump_174
            let assump_168 := assump_148 assump_291
            apply False.elim assump_168
        case inr assump_159 =>
          cases assump_159
          case inl assump_182 =>
            have assump_292 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_189
              intro assump_190
              cases assump_189
              case intro assump_193 assump_194 =>
                apply False.elim assump_194
            let assump_188 := assump_148 assump_292
            apply False.elim assump_188
          case inr assump_183 =>
            have assump_293 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_208
              intro assump_209
              cases assump_208
              case intro assump_212 assump_213 =>
                apply False.elim assump_213
            let assump_207 := assump_148 assump_293
            apply False.elim assump_207
      case inr assump_155 =>
        cases assump_153
        case inl assump_223 =>
          cases assump_223
          case intro assump_225 assump_226 =>
            have assump_294 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_234
              intro assump_235
              cases assump_234
              case intro assump_238 assump_239 =>
                apply False.elim assump_239
            let assump_233 := assump_148 assump_294
            apply False.elim assump_233
        case inr assump_224 =>
          cases assump_224
          case inl assump_247 =>
            have assump_295 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_254
              intro assump_255
              cases assump_254
              case intro assump_258 assump_259 =>
                apply False.elim assump_259
            let assump_253 := assump_148 assump_295
            apply False.elim assump_253
          case inr assump_248 =>
            have assump_296 : ((p7 ∧ False) → (p6 → p7)) := by
              intro assump_272
              intro assump_273
              cases assump_272
              case intro assump_276 assump_277 =>
                apply False.elim assump_277
            let assump_271 := assump_148 assump_296
            apply False.elim assump_271


variable (p1 p6 p3 p5 p0 p2 p4 p7 : Prop)
theorem file69_54087 : ((((((p7 → p1) → False) ∨ ((p6 → False) → (p0 ∧ p5))) → (((p3 ∨ p1) ∧ (p2 → False)) ∨ ((p0 ∨ p5) → (True → p3)))) ∧ ((((p1 ∧ False) ∧ (p3 ∧ p1)) ∧ ((p4 ∨ p7) → (p6 → p4))) ∧ (((True → p1) → (True ∨ p4)) ∨ ((False → False) → (False → p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p3 p4 p7 p0 p1 p5 : Prop)
theorem file69_54759 : (((((p5 → False) ∨ (False → False)) ∨ ((p5 ∧ p4) ∧ (p0 ∧ p0))) ∧ (((p3 ∨ p7) → (False ∧ p1)) ∧ ((False → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_65 : (False → False) := by
            intro assump_17
            apply False.elim assump_17
          let assump_16 := assump_11 assump_65
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_3
        case intro assump_25 assump_26 =>
          have assump_66 : (False → False) := by
            intro assump_32
            apply False.elim assump_32
          let assump_31 := assump_26 assump_66
          apply False.elim assump_31
    case inr assump_5 =>
      cases assump_5
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_39
          case intro assump_46 assump_47 =>
            cases assump_3
            case intro assump_52 assump_53 =>
              have assump_67 : (False → False) := by
                intro assump_59
                apply False.elim assump_59
              let assump_58 := assump_53 assump_67
              apply False.elim assump_58


variable (p7 p2 p5 p0 p3 p1 p4 : Prop)
theorem file69_56192 : (((((False → False) → False) → ((p7 ∨ p5) → (p5 ∨ p3))) ∨ (((p3 ∨ p0) ∧ (False ∨ True)) ∨ ((p1 → False) → (True → False)))) ∨ ((((False → False) → (p7 ∧ False)) → ((p0 ∧ False) ∧ (p2 ∧ p7))) ∨ (((p0 ∧ p4) → False) ∨ ((p3 → p5) ∧ (p1 → p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case inl assump_7 =>
    have assump_24 : (False → False) := by
      intro assump_14
      apply False.elim assump_14
    let assump_13 := assump_5 assump_24
    apply False.elim assump_13
  case inr assump_8 =>
    apply Or.inl
    exact assump_8


variable (p2 p0 p4 p7 p1 p5 p6 p3 : Prop)
theorem file69_56839 : (((((False → False) → (p0 → p5)) ∧ ((p4 → False) ∨ (True ∨ p0))) → (((p3 → False) ∨ (p2 → False)) → ((p7 → False) → (p2 ∨ p2)))) → ((((False ∨ p3) → (p7 ∧ True)) ∧ ((p7 ∧ True) ∨ (p1 ∧ True))) → (((p3 ∨ p6) → (p6 → p6)) ∧ ((False ∧ p2) → False)))) := by
  intro assump_148
  intro assump_149
  apply And.intro
  intro assump_150
  intro assump_151
  cases assump_150
  case inl assump_154 =>
    cases assump_149
    case intro assump_158 assump_159 =>
      cases assump_159
      case inl assump_162 =>
        cases assump_162
        case intro assump_164 assump_165 =>
          exact assump_151
      case inr assump_163 =>
        cases assump_163
        case intro assump_172 assump_173 =>
          exact assump_151
  case inr assump_155 =>
    cases assump_149
    case intro assump_182 assump_183 =>
      cases assump_183
      case inl assump_186 =>
        cases assump_186
        case intro assump_188 assump_189 =>
          exact assump_155
      case inr assump_187 =>
        cases assump_187
        case intro assump_196 assump_197 =>
          exact assump_155
  intro assump_204
  cases assump_204
  case intro assump_205 assump_206 =>
    apply False.elim assump_205


variable (p7 p2 p3 p5 p0 p4 : Prop)
theorem file69_58092 : ((((((p3 ∨ p0) ∨ (p0 ∨ p2)) → ((True → True) ∨ (p0 → p5))) → False) ∨ ((((p5 → p5) ∨ (p7 ∧ False)) ∨ ((p7 → True) ∧ (p4 ∨ True))) → (((True ∨ p4) ∨ (p5 ∨ p3)) → False))) → False) := by
  intro assump_26
  cases assump_26
  case inl assump_27 =>
    have assump_64 : (((p3 ∨ p0) ∨ (p0 ∨ p2)) → ((True → True) ∨ (p0 → p5))) := by
      intro assump_32
      cases assump_32
      case inl assump_33 =>
        cases assump_33
        case inl assump_35 =>
          apply Or.inl
          intro assump_39
          apply True.intro
        case inr assump_36 =>
          apply Or.inl
          intro assump_42
          apply True.intro
      case inr assump_34 =>
        cases assump_34
        case inl assump_43 =>
          apply Or.inl
          intro assump_47
          apply True.intro
        case inr assump_44 =>
          apply Or.inl
          intro assump_50
          apply True.intro
    let assump_31 := assump_27 assump_64
    apply False.elim assump_31
  case inr assump_28 =>
    have assump_65 : (((p5 → p5) ∨ (p7 ∧ False)) ∨ ((p7 → True) ∧ (p4 ∨ True))) := by
      apply Or.inl
      apply Or.inl
      intro assump_57
      exact assump_57
    let assump_56 := assump_28 assump_65
    have assump_66 : ((True ∨ p4) ∨ (p5 ∨ p3)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_60 := assump_56 assump_66
    apply False.elim assump_60


variable (p0 p2 p1 p5 p4 p7 p6 p3 : Prop)
theorem file69_59549 : (((((p0 ∧ p1) ∨ (p3 ∨ p6)) → ((p6 ∧ p7) → (p1 ∨ p4))) ∨ (((False → p5) → False) ∧ ((p2 ∧ p7) → (p3 ∧ p6)))) → ((((p2 → False) ∧ (p1 → p5)) → ((p4 → p1) → (p7 ∨ p1))) → (((True ∨ p2) ∨ (True → p6)) ∨ ((p5 → p4) ∨ (p5 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p2 p6 p7 p4 p0 p3 p1 p5 : Prop)
theorem file69_60152 : ((((((p6 → False) → (p4 → p5)) → ((p0 → True) → (p7 ∧ p1))) → (((False ∧ p6) → (p3 → False)) ∨ ((p0 ∨ p2) → (p1 → p6)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 → False) → (p4 → p5)) → ((p0 → True) → (p7 ∧ p1))) → (((False ∧ p6) → (p3 → False)) ∨ ((p0 ∨ p2) → (p1 → p6)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p7 p6 p3 p4 p0 p2 : Prop)
theorem file69_60750 : (((((True → p6) ∨ (p6 ∧ p3)) ∧ ((p6 → False) → (p1 ∧ p2))) ∨ (((p3 ∧ p2) → (True ∨ p1)) ∨ ((p1 → False) ∧ (p3 → p7)))) → ((((True → False) ∧ (p0 ∨ False)) → False) ∨ (((False → p6) ∨ (p0 → p4)) → ((False → p0) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          cases assump_14
          case inl assump_17 =>
            have assump_94 : True := by
              apply True.intro
            let assump_22 := assump_13 assump_94
            apply False.elim assump_22
          case inr assump_18 =>
            apply False.elim assump_18
      case inr assump_7 =>
        cases assump_7
        case intro assump_28 assump_29 =>
          apply Or.inl
          intro assump_36
          cases assump_36
          case intro assump_37 assump_38 =>
            cases assump_38
            case inl assump_41 =>
              have assump_95 : True := by
                apply True.intro
              let assump_46 := assump_37 assump_95
              apply False.elim assump_46
            case inr assump_42 =>
              apply False.elim assump_42
  case inr assump_3 =>
    cases assump_3
    case inl assump_52 =>
      apply Or.inl
      intro assump_56
      cases assump_56
      case intro assump_57 assump_58 =>
        cases assump_58
        case inl assump_61 =>
          have assump_96 : True := by
            apply True.intro
          let assump_66 := assump_57 assump_96
          apply False.elim assump_66
        case inr assump_62 =>
          apply False.elim assump_62
    case inr assump_53 =>
      cases assump_53
      case intro assump_72 assump_73 =>
        apply Or.inl
        intro assump_78
        cases assump_78
        case intro assump_79 assump_80 =>
          cases assump_80
          case inl assump_83 =>
            have assump_97 : True := by
              apply True.intro
            let assump_88 := assump_79 assump_97
            apply False.elim assump_88
          case inr assump_84 =>
            apply False.elim assump_84


variable (p2 p5 p3 p1 p6 p7 p4 p0 : Prop)
theorem file69_63048 : (((((p1 → p6) ∨ (p7 → False)) → False) ∧ (((p4 ∨ p3) ∨ (p0 ∧ False)) ∧ ((p6 ∨ p2) ∧ (p1 → False)))) → ((((p2 → p3) → (p7 ∨ p5)) ∨ ((False → False) ∨ (p7 ∨ p1))) ∨ (((p4 ∧ p3) → False) ∨ ((p2 ∧ True) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              apply Or.inl
              apply Or.inl
              intro assump_22
              have assump_118 : ((p1 → p6) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_30
                exact assump_16
              let assump_29 := assump_2 assump_118
              apply False.elim assump_29
            case inr assump_17 =>
              apply Or.inl
              apply Or.inl
              intro assump_40
              have assump_119 : ((p1 → p6) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_49
                have assump_120 : p1 := by
                  exact assump_49
                let assump_55 := assump_15 assump_120
                apply False.elim assump_55
              let assump_48 := assump_2 assump_119
              apply False.elim assump_48
        case inr assump_11 =>
          cases assump_7
          case intro assump_64 assump_65 =>
            cases assump_64
            case inl assump_66 =>
              apply Or.inl
              apply Or.inl
              intro assump_72
              have assump_121 : ((p1 → p6) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_80
                exact assump_66
              let assump_79 := assump_2 assump_121
              apply False.elim assump_79
            case inr assump_67 =>
              apply Or.inl
              apply Or.inl
              intro assump_90
              have assump_122 : ((p1 → p6) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_99
                have assump_123 : p1 := by
                  exact assump_99
                let assump_105 := assump_65 assump_123
                apply False.elim assump_105
              let assump_98 := assump_2 assump_122
              apply False.elim assump_98
      case inr assump_9 =>
        cases assump_9
        case intro assump_112 assump_113 =>
          apply False.elim assump_113


variable (p1 p6 p2 p7 p3 p0 : Prop)
theorem file69_65663 : (((((p1 ∧ True) ∨ (True → p7)) ∧ ((False → False) → (p2 → False))) → False) → ((((False ∧ p7) ∧ (False → p0)) → False) ∨ (((p3 ∨ False) ∨ (p0 ∨ p6)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p2 p4 p5 p1 p6 p3 p0 : Prop)
theorem file69_66079 : (((((p6 → False) → (p6 ∧ p2)) ∨ ((p2 ∧ p1) ∧ (False ∧ p4))) → (((p0 ∧ p0) ∨ (p6 → False)) → ((False → False) ∨ (p4 ∨ False)))) → ((((p2 ∧ p0) → (False → p4)) → ((True → False) → False)) ∨ (((p3 ∨ p3) ∨ (p5 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_15 : True := by
    apply True.intro
  let assump_11 := assump_5 assump_15
  apply False.elim assump_11


variable (p1 p7 p4 p5 p2 : Prop)
theorem file69_66553 : (((((True → False) → False) → False) → False) ∨ ((((False → False) → (p2 ∧ False)) → False) → (((p5 ∨ p1) → (True ∧ False)) ∧ ((p4 → p7) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((True → False) → False) := by
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p5 p7 p6 p2 p4 p1 : Prop)
theorem file69_67061 : ((((((p3 → p7) → (p4 ∨ p1)) → ((p5 ∨ p6) ∨ (p2 ∨ True))) ∨ (((p3 ∨ False) ∧ (True ∨ p2)) ∨ ((p6 → p4) → (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 → p7) → (p4 ∨ p1)) → ((p5 ∨ p6) ∨ (p2 ∨ True))) ∨ (((p3 ∨ False) ∧ (True ∨ p2)) ∨ ((p6 → p4) → (p2 → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p4 p6 p3 p5 : Prop)
theorem file69_67578 : ((((((False ∨ True) ∨ (p3 → p4)) → False) → (((p3 → False) ∨ (p6 ∧ p3)) ∨ ((p2 ∨ p4) ∨ (False → p5)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False ∨ True) ∨ (p3 → p4)) → False) → (((p3 → False) ∨ (p6 ∧ p3)) ∨ ((p2 ∨ p4) ∨ (False → p5)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_20 : ((False ∨ True) ∨ (p3 → p4)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p1 p6 p0 p7 p5 p3 : Prop)
theorem file69_68236 : (((((p0 → False) ∧ (p6 → False)) → ((p0 ∨ p5) ∧ (p1 ∧ p1))) ∧ (((True → p7) ∨ (True ∧ False)) ∧ ((p5 → p4) ∧ (False ∧ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
      case inr assump_9 =>
        cases assump_9
        case intro assump_20 assump_21 =>
          apply False.elim assump_21


variable (p6 p1 p2 p5 p0 p3 p7 : Prop)
theorem file69_68913 : ((((((p7 ∧ p0) → (p2 → False)) ∧ ((p5 ∨ p2) ∧ (p2 ∧ p1))) ∧ (((p6 → False) ∧ (p2 ∨ False)) ∧ ((p1 → False) → (True ∨ p7)))) ∧ ((((True ∧ p1) → (p7 → False)) → ((True → False) ∨ (p7 → p3))) ∧ (((p1 ∨ p6) ∧ (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              cases assump_5
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case inl assump_28 =>
                    cases assump_3
                    case intro assump_34 assump_35 =>
                      have assump_84 : ((p1 ∨ p6) ∧ (False → False)) := by
                        apply And.intro
                        apply Or.inl
                        exact assump_17
                        intro assump_41
                        apply False.elim assump_41
                      let assump_40 := assump_35 assump_84
                      apply False.elim assump_40
                  case inr assump_29 =>
                    apply False.elim assump_29
          case inr assump_13 =>
            cases assump_11
            case intro assump_51 assump_52 =>
              cases assump_5
              case intro assump_57 assump_58 =>
                cases assump_57
                case intro assump_59 assump_60 =>
                  cases assump_60
                  case inl assump_63 =>
                    cases assump_3
                    case intro assump_69 assump_70 =>
                      have assump_85 : ((p1 ∨ p6) ∧ (False → False)) := by
                        apply And.intro
                        apply Or.inl
                        exact assump_52
                        intro assump_76
                        apply False.elim assump_76
                      let assump_75 := assump_70 assump_85
                      apply False.elim assump_75
                  case inr assump_64 =>
                    apply False.elim assump_64


variable (p3 p0 p5 p6 p1 p7 : Prop)
theorem file69_71306 : ((((((p1 ∧ p3) ∨ (p7 ∧ p3)) ∧ ((p3 ∧ p6) ∨ (True ∧ p5))) → False) ∧ ((((p5 → p5) → (False ∧ p6)) → ((p0 ∧ p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p5 → p5) → (False ∧ p6)) → ((p0 ∧ p7) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_31 : (p5 → p5) := by
          intro assump_20
          exact assump_20
        let assump_19 := assump_9 assump_31
        let assump_23 := And.left assump_19
        apply False.elim assump_23
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


variable (p7 p5 p1 p6 p4 p0 : Prop)
theorem file69_72047 : (((((True → p4) ∨ (p1 ∨ False)) ∨ ((p5 → False) → (p0 → False))) ∧ (((p7 → p7) → False) ∧ ((p0 → False) ∧ (True → False)))) → ((((False → True) ∨ (True → True)) → ((p0 → False) ∧ (False ∧ p7))) → (((p4 ∨ p7) → (p0 → False)) ∨ ((True ∧ p6) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_6
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply Or.inl
            intro assump_23
            intro assump_24
            cases assump_23
            case inl assump_27 =>
              have assump_117 : True := by
                apply True.intro
              let assump_33 := assump_18 assump_117
              apply False.elim assump_33
            case inr assump_28 =>
              have assump_118 : True := by
                apply True.intro
              let assump_41 := assump_18 assump_118
              apply False.elim assump_41
      case inr assump_10 =>
        cases assump_10
        case inl assump_45 =>
          cases assump_6
          case intro assump_49 assump_50 =>
            cases assump_50
            case intro assump_53 assump_54 =>
              apply Or.inl
              intro assump_59
              intro assump_60
              cases assump_59
              case inl assump_63 =>
                have assump_119 : True := by
                  apply True.intro
                let assump_69 := assump_54 assump_119
                apply False.elim assump_69
              case inr assump_64 =>
                have assump_120 : True := by
                  apply True.intro
                let assump_77 := assump_54 assump_120
                apply False.elim assump_77
        case inr assump_46 =>
          apply False.elim assump_46
    case inr assump_8 =>
      cases assump_6
      case intro assump_85 assump_86 =>
        cases assump_86
        case intro assump_89 assump_90 =>
          apply Or.inl
          intro assump_95
          intro assump_96
          cases assump_95
          case inl assump_99 =>
            have assump_121 : True := by
              apply True.intro
            let assump_105 := assump_90 assump_121
            apply False.elim assump_105
          case inr assump_100 =>
            have assump_122 : True := by
              apply True.intro
            let assump_113 := assump_90 assump_122
            apply False.elim assump_113


variable (p5 p2 p7 p1 p6 p4 p3 : Prop)
theorem file69_74673 : (((((p2 ∧ p2) → (False ∨ True)) → ((True → False) → (p1 → p1))) → False) → ((((p7 → False) ∨ (p6 ∧ p1)) → ((p5 ∧ p5) ∨ (p7 ∨ p5))) ∧ (((p6 ∨ p4) ∨ (False ∧ p3)) → False))) := by
  intro assump_7
  apply And.intro
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    have assump_92 : (((p2 ∧ p2) → (False ∨ True)) → ((True → False) → (p1 → p1))) := by
      intro assump_16
      intro assump_17
      intro assump_18
      exact assump_18
    let assump_15 := assump_7 assump_92
    apply False.elim assump_15
  case inr assump_10 =>
    cases assump_10
    case intro assump_28 assump_29 =>
      have assump_93 : (((p2 ∧ p2) → (False ∨ True)) → ((True → False) → (p1 → p1))) := by
        intro assump_37
        intro assump_38
        intro assump_39
        exact assump_39
      let assump_36 := assump_7 assump_93
      apply False.elim assump_36
  intro assump_49
  cases assump_49
  case inl assump_50 =>
    cases assump_50
    case inl assump_52 =>
      have assump_94 : (((p2 ∧ p2) → (False ∨ True)) → ((True → False) → (p1 → p1))) := by
        intro assump_59
        intro assump_60
        intro assump_61
        exact assump_61
      let assump_58 := assump_7 assump_94
      apply False.elim assump_58
    case inr assump_53 =>
      have assump_95 : (((p2 ∧ p2) → (False ∨ True)) → ((True → False) → (p1 → p1))) := by
        intro assump_76
        intro assump_77
        intro assump_78
        exact assump_78
      let assump_75 := assump_7 assump_95
      apply False.elim assump_75
  case inr assump_51 =>
    cases assump_51
    case intro assump_88 assump_89 =>
      apply False.elim assump_88


variable (p1 p4 p6 p2 p7 p3 : Prop)
theorem file69_76366 : ((((((p6 ∨ p3) ∧ (True ∧ p1)) ∨ ((p4 ∨ True) ∨ (p6 → p1))) → False) ∧ ((((p7 ∧ p2) ∧ (p1 ∧ p3)) ∧ ((p2 ∨ p6) ∧ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p6 ∨ p3) ∧ (True ∧ p1)) ∨ ((p4 ∨ True) ∨ (p6 → p1))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_9 := assump_2 assump_13
    apply False.elim assump_9


variable (p0 p1 p6 p3 : Prop)
theorem file69_76874 : (((((p3 ∧ p1) → (p0 → p3)) ∧ ((p6 → False) ∨ (p6 → p1))) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_40 : ((True → False) → False) := by
          intro assump_15
          have assump_41 : True := by
            apply True.intro
          let assump_18 := assump_15 assump_41
          apply False.elim assump_18
        let assump_14 := assump_3 assump_40
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_42 : ((True → False) → False) := by
          intro assump_30
          have assump_43 : True := by
            apply True.intro
          let assump_33 := assump_30 assump_43
          apply False.elim assump_33
        let assump_29 := assump_3 assump_42
        apply False.elim assump_29


variable (p2 p3 p5 p0 p6 p4 : Prop)
theorem file69_77866 : (((((p2 → False) → (False → False)) ∧ ((p5 ∨ p0) → False)) → (((p5 → p3) ∨ (False ∧ False)) ∨ ((p4 → False) → False))) ∨ ((((p2 ∧ p6) ∧ (False → False)) → ((p2 → False) → False)) ∧ (((p0 → False) ∧ (p5 ∧ p5)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_16 : (p5 ∨ p0) := by
      apply Or.inl
      exact assump_8
    let assump_12 := assump_3 assump_16
    apply False.elim assump_12


variable (p1 p0 p7 p6 p5 p3 p2 p4 : Prop)
theorem file69_78442 : (((((p3 → False) → (p5 ∨ False)) ∨ ((p0 ∨ p2) → False)) → (((p6 ∧ p2) ∨ (p7 → False)) → False)) → ((((p0 → False) ∧ (p6 ∨ p6)) ∧ ((p1 ∨ p0) → (True → False))) → (((True ∧ p3) → (True ∨ p0)) ∨ ((p2 → False) ∨ (p4 ∨ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        apply Or.inl
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          apply Or.inl
          apply True.intro
      case inr assump_10 =>
        apply Or.inl
        intro assump_30
        cases assump_30
        case intro assump_31 assump_32 =>
          apply Or.inl
          apply True.intro


variable (p2 p1 : Prop)
theorem file69_79259 : ((((((True → False) → False) → False) → (((p2 → p2) ∨ (False → False)) ∧ ((p1 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((True → False) → False) → False) → (((p2 → p2) ∨ (False → False)) ∧ ((p1 → False) → False))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    exact assump_8
    intro assump_11
    have assump_31 : ((True → False) → False) := by
      intro assump_17
      have assump_32 : True := by
        apply True.intro
      let assump_20 := assump_17 assump_32
      apply False.elim assump_20
    let assump_16 := assump_5 assump_31
    apply False.elim assump_16
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p4 p1 p2 p0 p7 p6 : Prop)
theorem file69_80038 : (((((p0 → p2) → (p0 ∧ p1)) ∨ ((False ∨ p4) ∧ (False → p0))) ∧ (((p4 ∨ p7) → (p6 → False)) ∧ ((True → False) ∧ (p6 → False)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          have assump_52 : True := by
            apply True.intro
          let assump_23 := assump_16 assump_52
          apply False.elim assump_23
    case inr assump_9 =>
      cases assump_9
      case intro assump_27 assump_28 =>
        cases assump_27
        case inl assump_29 =>
          apply False.elim assump_29
        case inr assump_30 =>
          cases assump_7
          case intro assump_37 assump_38 =>
            cases assump_38
            case intro assump_41 assump_42 =>
              have assump_53 : True := by
                apply True.intro
              let assump_48 := assump_41 assump_53
              apply False.elim assump_48


variable (p4 p7 p0 p5 p1 p2 p6 : Prop)
theorem file69_81149 : ((((((p0 ∧ p1) → (p5 → False)) ∧ ((p2 ∧ False) ∧ (p4 ∨ p7))) ∧ (((False → p6) ∨ (p1 → p6)) → False)) ∧ ((((p5 → p2) ∧ (p2 ∧ True)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p3 p0 : Prop)
theorem file69_81718 : ((((((False ∧ p0) ∨ (False → False)) → ((p3 → p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False ∧ p0) ∨ (False → False)) → ((p3 → p3) → False)) → False) := by
    intro assump_5
    have assump_23 : ((False ∧ p0) ∨ (False → False)) := by
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_23
    have assump_24 : (p3 → p3) := by
      intro assump_13
      exact assump_13
    let assump_12 := assump_8 assump_24
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p1 p4 p6 p5 : Prop)
theorem file69_82384 : (((((p7 ∧ p6) → (p1 → False)) ∨ ((False → p5) → False)) ∧ (((False ∧ p4) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_32 : ((False ∧ p4) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      let assump_10 := assump_3 assump_32
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_33 : ((False ∧ p4) → False) := by
        intro assump_24
        cases assump_24
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
      let assump_23 := assump_3 assump_33
      apply False.elim assump_23


variable (p3 p4 p6 p7 p2 p5 p1 p0 : Prop)
theorem file69_83202 : (((((p2 ∧ p7) ∨ (False ∧ p3)) ∧ ((p1 ∧ p3) → (p7 → False))) → (((p3 ∨ True) ∧ (True → False)) → ((True → False) → (p4 → p0)))) ∧ ((((False ∨ False) → (p6 ∧ False)) ∧ ((p0 ∨ p5) → False)) → (((p5 ∧ p7) → False) → ((False → False) ∨ (p3 ∨ p2))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        cases assump_17
        case inl assump_19 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            have assump_80 : True := by
              apply True.intro
            let assump_32 := assump_10 assump_80
            apply False.elim assump_32
        case inr assump_20 =>
          cases assump_20
          case intro assump_36 assump_37 =>
            apply False.elim assump_36
    case inr assump_12 =>
      cases assump_1
      case intro assump_44 assump_45 =>
        cases assump_44
        case inl assump_46 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            have assump_81 : True := by
              apply True.intro
            let assump_59 := assump_10 assump_81
            apply False.elim assump_59
        case inr assump_47 =>
          cases assump_47
          case intro assump_63 assump_64 =>
            apply False.elim assump_63
  intro assump_67
  intro assump_68
  cases assump_67
  case intro assump_71 assump_72 =>
    apply Or.inl
    intro assump_77
    apply False.elim assump_77


variable (p6 : Prop)
theorem file69_84831 : (((((False → p6) → False) → False) ∧ (((True ∧ False) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_23 : ((True ∧ False) → False) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    let assump_12 := assump_7 assump_23
    apply False.elim assump_12


variable (p4 p0 p1 p5 p6 p2 p7 : Prop)
theorem file69_85292 : (((((p2 ∧ True) ∨ (p7 → p7)) ∨ ((p1 ∨ False) → False)) ∨ (((True → False) → (p4 ∨ p2)) ∧ ((p2 → p7) → False))) → ((((True ∨ p5) ∨ (True → p0)) ∨ ((p7 ∨ True) → False)) ∧ (((p7 ∨ p0) ∧ (p2 ∧ p5)) → ((p4 → True) ∨ (p6 ∧ p1))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_7 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_18 assump_19 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case inl assump_27 =>
      cases assump_26
      case intro assump_31 assump_32 =>
        cases assump_1
        case inl assump_37 =>
          cases assump_37
          case inl assump_39 =>
            cases assump_39
            case inl assump_41 =>
              cases assump_41
              case intro assump_43 assump_44 =>
                apply Or.inl
                intro assump_49
                apply True.intro
            case inr assump_42 =>
              apply Or.inl
              intro assump_52
              apply True.intro
          case inr assump_40 =>
            apply Or.inl
            intro assump_55
            apply True.intro
        case inr assump_38 =>
          cases assump_38
          case intro assump_56 assump_57 =>
            apply Or.inl
            intro assump_62
            apply True.intro
    case inr assump_28 =>
      cases assump_26
      case intro assump_65 assump_66 =>
        cases assump_1
        case inl assump_71 =>
          cases assump_71
          case inl assump_73 =>
            cases assump_73
            case inl assump_75 =>
              cases assump_75
              case intro assump_77 assump_78 =>
                apply Or.inl
                intro assump_83
                apply True.intro
            case inr assump_76 =>
              apply Or.inl
              intro assump_86
              apply True.intro
          case inr assump_74 =>
            apply Or.inl
            intro assump_89
            apply True.intro
        case inr assump_72 =>
          cases assump_72
          case intro assump_90 assump_91 =>
            apply Or.inl
            intro assump_96
            apply True.intro


variable (p3 p5 p4 p2 p6 p7 p1 : Prop)
theorem file69_88087 : ((((((p7 ∧ p6) → (p7 ∨ p5)) ∧ ((p2 ∧ True) → False)) ∨ (((p3 ∧ p1) ∨ (p2 ∨ True)) → ((p6 → False) ∨ (False ∧ p6)))) ∧ ((((p4 ∧ False) ∨ (p7 ∧ p3)) → ((p1 ∧ False) → (p3 ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_54 : (((p4 ∧ False) ∨ (p7 ∧ p3)) → ((p1 ∧ False) → (p3 ∧ p5))) := by
          intro assump_15
          intro assump_16
          apply And.intro
          cases assump_16
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
          cases assump_16
          case intro assump_23 assump_24 =>
            apply False.elim assump_24
        let assump_14 := assump_3 assump_54
        apply False.elim assump_14
    case inr assump_5 =>
      have assump_55 : (((p4 ∧ False) ∨ (p7 ∧ p3)) → ((p1 ∧ False) → (p3 ∧ p5))) := by
        intro assump_37
        intro assump_38
        apply And.intro
        cases assump_38
        case intro assump_39 assump_40 =>
          apply False.elim assump_40
        cases assump_38
        case intro assump_45 assump_46 =>
          apply False.elim assump_46
      let assump_36 := assump_3 assump_55
      apply False.elim assump_36


variable (p6 p7 p5 p2 p1 p3 p0 : Prop)
theorem file69_89452 : ((((((True → p2) → False) ∧ ((p2 ∧ False) ∧ (p3 ∧ p5))) ∧ (((p5 → True) → False) → ((p3 → p1) ∨ (p6 ∧ p6)))) ∧ ((((p7 → False) ∧ (True ∧ p1)) ∧ ((p0 ∨ p7) → (False ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p5 p0 p7 p4 p3 : Prop)
theorem file69_90064 : (((((p0 → False) → False) ∨ ((p7 → False) ∧ (p4 ∧ p5))) ∧ (((True → False) → (False → p5)) ∧ ((p0 → p3) ∧ (False ∧ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
    case inr assump_5 =>
      cases assump_5
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          cases assump_3
          case intro assump_30 assump_31 =>
            cases assump_31
            case intro assump_34 assump_35 =>
              cases assump_35
              case intro assump_38 assump_39 =>
                apply False.elim assump_38


variable (p1 p3 p6 p5 p2 p7 : Prop)
theorem file69_91022 : (((((p1 ∧ p7) → False) ∨ ((False → p1) → False)) → (((p1 ∨ p2) ∧ (True → False)) → False)) ∨ ((((p7 → False) → (True → False)) → False) → (((p6 → False) → (p7 ∧ p3)) → ((p2 ∧ p1) ∨ (p7 → p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case inl assump_11 =>
        have assump_51 : True := by
          apply True.intro
        let assump_16 := assump_4 assump_51
        apply False.elim assump_16
      case inr assump_12 =>
        have assump_52 : (False → p1) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_12 assump_52
        apply False.elim assump_22
    case inr assump_6 =>
      cases assump_1
      case inl assump_33 =>
        have assump_53 : True := by
          apply True.intro
        let assump_38 := assump_4 assump_53
        apply False.elim assump_38
      case inr assump_34 =>
        have assump_54 : (False → p1) := by
          intro assump_45
          apply False.elim assump_45
        let assump_44 := assump_34 assump_54
        apply False.elim assump_44


variable (p1 p6 p4 p0 p5 : Prop)
theorem file69_92261 : ((((((p4 → p1) → (p6 ∨ True)) → False) → (((p5 → p6) ∨ (p4 ∨ p0)) ∧ ((True → False) → False))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p4 → p1) → (p6 ∨ True)) → False) → (((p5 → p6) ∨ (p4 ∨ p0)) ∧ ((True → False) → False))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    have assump_35 : ((p4 → p1) → (p6 ∨ True)) := by
      intro assump_13
      apply Or.inr
      apply True.intro
    let assump_12 := assump_5 assump_35
    apply False.elim assump_12
    intro assump_19
    have assump_36 : ((p4 → p1) → (p6 ∨ True)) := by
      intro assump_25
      apply Or.inr
      apply True.intro
    let assump_24 := assump_5 assump_36
    apply False.elim assump_24
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p7 p0 p1 p6 p2 : Prop)
theorem file69_93108 : (((((p2 ∧ False) ∨ (p1 ∨ p2)) ∧ ((True ∧ True) → False)) ∧ (((p7 ∧ p2) → (p0 ∨ p7)) ∧ ((False ∨ p6) → (False ∨ True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9
      case inr assump_7 =>
        cases assump_7
        case inl assump_14 =>
          cases assump_3
          case intro assump_20 assump_21 =>
            have assump_48 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_28 := assump_5 assump_48
            apply False.elim assump_28
        case inr assump_15 =>
          cases assump_3
          case intro assump_36 assump_37 =>
            have assump_49 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_44 := assump_5 assump_49
            apply False.elim assump_44


variable (p4 p0 p6 p3 p1 p2 : Prop)
theorem file69_94277 : (((((p0 → p3) ∨ (p1 → False)) → False) ∧ (((True ∨ False) ∨ (p6 ∨ p1)) → False)) → ((((True ∧ p2) → False) → False) ∨ (((False → False) ∨ (p4 ∧ True)) ∨ ((p1 ∧ p0) ∨ (p4 → p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_16 : ((True ∨ False) ∨ (p6 ∨ p1)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_12 := assump_3 assump_16
    apply False.elim assump_12


variable (p4 p6 p7 p3 p0 p2 p5 p1 : Prop)
theorem file69_94821 : (((((True → p4) ∨ (p3 ∧ p0)) ∨ ((True ∨ p7) → False)) ∨ (((p3 → p2) → False) → False)) → ((((True ∨ p7) → False) → ((p6 ∧ p1) ∧ (p3 → False))) ∨ (((p2 ∨ p6) → False) ∧ ((p2 ∨ p5) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_10
        apply And.intro
        apply And.intro
        have assump_108 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_13 := assump_10 assump_108
        apply False.elim assump_13
        have assump_109 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_19 := assump_10 assump_109
        apply False.elim assump_19
        intro assump_23
        have assump_110 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_28 := assump_10 assump_110
        apply False.elim assump_28
      case inr assump_7 =>
        cases assump_7
        case intro assump_32 assump_33 =>
          apply Or.inl
          intro assump_38
          apply And.intro
          apply And.intro
          have assump_111 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_41 := assump_38 assump_111
          apply False.elim assump_41
          have assump_112 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_47 := assump_38 assump_112
          apply False.elim assump_47
          intro assump_51
          have assump_113 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_56 := assump_38 assump_113
          apply False.elim assump_56
    case inr assump_5 =>
      apply Or.inl
      intro assump_62
      apply And.intro
      apply And.intro
      have assump_114 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_65 := assump_62 assump_114
      apply False.elim assump_65
      have assump_115 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_71 := assump_62 assump_115
      apply False.elim assump_71
      intro assump_75
      have assump_116 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_80 := assump_62 assump_116
      apply False.elim assump_80
  case inr assump_3 =>
    apply Or.inl
    intro assump_86
    apply And.intro
    apply And.intro
    have assump_117 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_89 := assump_86 assump_117
    apply False.elim assump_89
    have assump_118 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_95 := assump_86 assump_118
    apply False.elim assump_95
    intro assump_99
    have assump_119 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_104 := assump_86 assump_119
    apply False.elim assump_104


variable (p7 p2 p0 p4 p6 p5 p1 p3 : Prop)
theorem file69_97863 : (((((p0 ∨ p6) → False) ∨ ((p7 ∧ p1) ∧ (p0 → p0))) → (((True → False) → (p5 → p1)) ∨ ((p7 → p4) → False))) ∨ ((((p1 → p1) → (True → False)) → ((p1 → False) → (p4 → p7))) ∨ (((p3 ∨ p1) ∨ (p7 → False)) → ((p3 ∨ p1) → (p2 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    have assump_32 : True := by
      apply True.intro
    let assump_12 := assump_6 assump_32
    apply False.elim assump_12
  case inr assump_3 =>
    cases assump_3
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        apply Or.inl
        intro assump_26
        intro assump_27
        exact assump_19


variable (p2 p5 p3 p1 p6 p4 p0 p7 : Prop)
theorem file69_98651 : ((((((p5 → p7) ∧ (p2 ∨ p3)) ∧ ((p6 ∧ False) ∧ (p3 ∨ p1))) → False) ∧ ((((p0 ∧ False) ∧ (p5 → p1)) ∧ ((True ∨ p7) ∨ (p7 → False))) ∧ (((True → False) ∧ (p4 ∧ p4)) → ((p1 ∨ True) ∧ (p4 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p4 p3 p1 p5 p6 p0 p7 : Prop)
theorem file69_99280 : (((((True ∨ p3) → False) ∧ ((p5 → False) ∧ (p6 ∨ p3))) → (((True → False) ∧ (p5 ∨ p0)) ∨ ((p0 ∧ p3) ∨ (p7 → p0)))) ∨ ((((p4 ∧ p5) → False) → False) ∧ (((p7 ∨ True) → (p1 → False)) ∨ ((p4 ∧ True) ∨ (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inr
        apply Or.inr
        intro assump_23
        have assump_54 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_29 := assump_2 assump_54
        apply False.elim assump_29
      case inr assump_11 =>
        apply Or.inr
        apply Or.inr
        intro assump_44
        have assump_55 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_50 := assump_2 assump_55
        apply False.elim assump_50


variable (p2 p6 p1 p7 p3 p0 : Prop)
theorem file69_100251 : (((((True ∨ p7) → False) → ((p6 → False) ∧ (False ∧ p3))) → (((False → False) → (p1 ∧ p2)) → ((p7 → False) → (p6 → False)))) → ((((True ∨ p3) ∨ (p6 ∨ p2)) → ((p1 → p0) ∧ (p1 → False))) → (((p2 ∨ p1) → (False ∧ p2)) → ((False → p6) ∨ (False ∧ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inl
  intro assump_10
  apply False.elim assump_10


variable (p7 p3 p4 p6 p2 p1 : Prop)
theorem file69_100680 : (((((p2 → False) → (p2 → p4)) ∧ ((p7 → p2) → False)) ∧ (((p1 ∧ p3) → (p1 ∧ p6)) ∧ ((p1 → False) → (p1 ∨ p2)))) → ((((p7 ∧ False) → False) ∨ ((p3 ∧ p2) ∨ (p4 ∨ p3))) ∨ (((p3 → p7) ∨ (p6 → False)) ∨ ((p2 → p3) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inl
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          apply False.elim assump_18


variable (p1 p3 p0 p7 p4 p6 p2 p5 : Prop)
theorem file69_101325 : (((((p5 ∧ p2) → (False → p2)) ∨ ((p4 ∧ p5) → (p1 → p6))) ∨ (((p5 → p2) ∨ (True ∧ p2)) → False)) ∨ ((((p3 → False) ∧ (p5 ∧ p5)) ∨ ((True → False) ∨ (True ∧ p3))) ∨ (((True → p7) ∨ (True → p5)) ∨ ((p2 ∧ p0) → (False → p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p4 p5 p1 p6 p2 p0 : Prop)
theorem file69_101722 : (((((p6 ∨ p0) ∧ (p5 → False)) ∧ ((p0 ∨ True) → False)) → False) ∨ ((((p0 → False) ∧ (p1 ∧ p4)) ∨ ((p1 → False) ∨ (p0 ∨ p2))) ∧ (((p4 ∧ p0) ∨ (p1 ∧ p5)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_28 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_14 := assump_3 assump_28
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_29 : (p0 ∨ True) := by
          apply Or.inl
          exact assump_7
        let assump_24 := assump_3 assump_29
        apply False.elim assump_24


variable (p3 p7 p2 p1 p0 p4 : Prop)
theorem file69_102506 : (((((p0 ∧ False) ∧ (False ∧ p3)) ∧ ((p1 ∨ p0) ∨ (p3 → p2))) ∧ (((p1 ∨ p4) → False) → ((False → p4) ∧ (p7 ∧ p0)))) → ((((p1 → False) → (p2 → False)) → False) ∨ (((p4 → False) → (False → False)) → False))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply False.elim assump_17


variable (p2 p5 p7 p3 p4 : Prop)
theorem file69_103066 : ((((((p3 ∧ p4) ∧ (p5 ∨ True)) → False) → False) ∧ ((((p5 ∨ p4) ∨ (False ∧ p2)) → ((False ∨ False) → (p4 → p7))) → False)) → False) := by
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    have assump_48 : (((p5 ∨ p4) ∨ (False ∧ p2)) → ((False ∨ False) → (p4 → p7))) := by
      intro assump_34
      intro assump_35
      intro assump_36
      cases assump_35
      case inl assump_39 =>
        apply False.elim assump_39
      case inr assump_40 =>
        apply False.elim assump_40
    let assump_33 := assump_28 assump_48
    apply False.elim assump_33


variable (p1 p7 p0 p3 p4 p2 p6 p5 : Prop)
theorem file69_103715 : (((((p2 ∨ True) → False) → ((False ∧ p2) → (p6 ∨ p0))) ∨ (((p5 ∨ p4) → (p6 ∧ p7)) → False)) ∨ ((((p3 ∨ p3) ∨ (True → False)) ∨ ((p1 → True) → (p2 ∧ p0))) → (((p3 → p4) ∨ (p2 → False)) → ((p7 → False) ∨ (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p6 p4 p1 p5 p7 p0 p2 : Prop)
theorem file69_104148 : (((((p6 → p2) → False) ∧ ((p4 → False) ∨ (p6 ∨ p0))) ∧ (((p0 → False) ∨ (p1 ∧ p7)) ∧ ((p5 → False) ∧ (p4 ∨ p1)))) → ((((p2 → True) ∧ (p0 → p4)) ∧ ((p5 → False) ∧ (p6 ∨ p2))) → (((True → False) → False) ∨ ((p1 ∨ p1) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          cases assump_1
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_22
              case inl assump_25 =>
                cases assump_20
                case intro assump_29 assump_30 =>
                  cases assump_29
                  case inl assump_31 =>
                    cases assump_30
                    case intro assump_35 assump_36 =>
                      cases assump_36
                      case inl assump_39 =>
                        apply Or.inl
                        intro assump_43
                        have assump_413 : True := by
                          apply True.intro
                        let assump_46 := assump_43 assump_413
                        apply False.elim assump_46
                      case inr assump_40 =>
                        apply Or.inl
                        intro assump_52
                        have assump_414 : True := by
                          apply True.intro
                        let assump_55 := assump_52 assump_414
                        apply False.elim assump_55
                  case inr assump_32 =>
                    cases assump_32
                    case intro assump_59 assump_60 =>
                      cases assump_30
                      case intro assump_65 assump_66 =>
                        cases assump_66
                        case inl assump_69 =>
                          apply Or.inl
                          intro assump_73
                          have assump_415 : True := by
                            apply True.intro
                          let assump_76 := assump_73 assump_415
                          apply False.elim assump_76
                        case inr assump_70 =>
                          apply Or.inl
                          intro assump_82
                          have assump_416 : True := by
                            apply True.intro
                          let assump_85 := assump_82 assump_416
                          apply False.elim assump_85
              case inr assump_26 =>
                cases assump_26
                case inl assump_89 =>
                  cases assump_20
                  case intro assump_93 assump_94 =>
                    cases assump_93
                    case inl assump_95 =>
                      cases assump_94
                      case intro assump_99 assump_100 =>
                        cases assump_100
                        case inl assump_103 =>
                          apply Or.inl
                          intro assump_107
                          have assump_417 : True := by
                            apply True.intro
                          let assump_110 := assump_107 assump_417
                          apply False.elim assump_110
                        case inr assump_104 =>
                          apply Or.inl
                          intro assump_116
                          have assump_418 : True := by
                            apply True.intro
                          let assump_119 := assump_116 assump_418
                          apply False.elim assump_119
                    case inr assump_96 =>
                      cases assump_96
                      case intro assump_123 assump_124 =>
                        cases assump_94
                        case intro assump_129 assump_130 =>
                          cases assump_130
                          case inl assump_133 =>
                            apply Or.inl
                            intro assump_137
                            have assump_419 : True := by
                              apply True.intro
                            let assump_140 := assump_137 assump_419
                            apply False.elim assump_140
                          case inr assump_134 =>
                            apply Or.inl
                            intro assump_146
                            have assump_420 : True := by
                              apply True.intro
                            let assump_149 := assump_146 assump_420
                            apply False.elim assump_149
                case inr assump_90 =>
                  cases assump_20
                  case intro assump_155 assump_156 =>
                    cases assump_155
                    case inl assump_157 =>
                      cases assump_156
                      case intro assump_161 assump_162 =>
                        cases assump_162
                        case inl assump_165 =>
                          apply Or.inl
                          intro assump_169
                          have assump_421 : True := by
                            apply True.intro
                          let assump_172 := assump_169 assump_421
                          apply False.elim assump_172
                        case inr assump_166 =>
                          apply Or.inl
                          intro assump_178
                          have assump_422 : True := by
                            apply True.intro
                          let assump_181 := assump_178 assump_422
                          apply False.elim assump_181
                    case inr assump_158 =>
                      cases assump_158
                      case intro assump_185 assump_186 =>
                        cases assump_156
                        case intro assump_191 assump_192 =>
                          cases assump_192
                          case inl assump_195 =>
                            apply Or.inl
                            intro assump_199
                            have assump_423 : True := by
                              apply True.intro
                            let assump_202 := assump_199 assump_423
                            apply False.elim assump_202
                          case inr assump_196 =>
                            apply Or.inl
                            intro assump_208
                            have assump_424 : True := by
                              apply True.intro
                            let assump_211 := assump_208 assump_424
                            apply False.elim assump_211
        case inr assump_16 =>
          cases assump_1
          case intro assump_217 assump_218 =>
            cases assump_217
            case intro assump_219 assump_220 =>
              cases assump_220
              case inl assump_223 =>
                cases assump_218
                case intro assump_227 assump_228 =>
                  cases assump_227
                  case inl assump_229 =>
                    cases assump_228
                    case intro assump_233 assump_234 =>
                      cases assump_234
                      case inl assump_237 =>
                        apply Or.inl
                        intro assump_241
                        have assump_425 : True := by
                          apply True.intro
                        let assump_244 := assump_241 assump_425
                        apply False.elim assump_244
                      case inr assump_238 =>
                        apply Or.inl
                        intro assump_250
                        have assump_426 : True := by
                          apply True.intro
                        let assump_253 := assump_250 assump_426
                        apply False.elim assump_253
                  case inr assump_230 =>
                    cases assump_230
                    case intro assump_257 assump_258 =>
                      cases assump_228
                      case intro assump_263 assump_264 =>
                        cases assump_264
                        case inl assump_267 =>
                          apply Or.inl
                          intro assump_271
                          have assump_427 : True := by
                            apply True.intro
                          let assump_274 := assump_271 assump_427
                          apply False.elim assump_274
                        case inr assump_268 =>
                          apply Or.inl
                          intro assump_280
                          have assump_428 : True := by
                            apply True.intro
                          let assump_283 := assump_280 assump_428
                          apply False.elim assump_283
              case inr assump_224 =>
                cases assump_224
                case inl assump_287 =>
                  cases assump_218
                  case intro assump_291 assump_292 =>
                    cases assump_291
                    case inl assump_293 =>
                      cases assump_292
                      case intro assump_297 assump_298 =>
                        cases assump_298
                        case inl assump_301 =>
                          apply Or.inl
                          intro assump_305
                          have assump_429 : True := by
                            apply True.intro
                          let assump_308 := assump_305 assump_429
                          apply False.elim assump_308
                        case inr assump_302 =>
                          apply Or.inl
                          intro assump_314
                          have assump_430 : True := by
                            apply True.intro
                          let assump_317 := assump_314 assump_430
                          apply False.elim assump_317
                    case inr assump_294 =>
                      cases assump_294
                      case intro assump_321 assump_322 =>
                        cases assump_292
                        case intro assump_327 assump_328 =>
                          cases assump_328
                          case inl assump_331 =>
                            apply Or.inl
                            intro assump_335
                            have assump_431 : True := by
                              apply True.intro
                            let assump_338 := assump_335 assump_431
                            apply False.elim assump_338
                          case inr assump_332 =>
                            apply Or.inl
                            intro assump_344
                            have assump_432 : True := by
                              apply True.intro
                            let assump_347 := assump_344 assump_432
                            apply False.elim assump_347
                case inr assump_288 =>
                  cases assump_218
                  case intro assump_353 assump_354 =>
                    cases assump_353
                    case inl assump_355 =>
                      cases assump_354
                      case intro assump_359 assump_360 =>
                        cases assump_360
                        case inl assump_363 =>
                          apply Or.inl
                          intro assump_367
                          have assump_433 : True := by
                            apply True.intro
                          let assump_370 := assump_367 assump_433
                          apply False.elim assump_370
                        case inr assump_364 =>
                          apply Or.inl
                          intro assump_376
                          have assump_434 : True := by
                            apply True.intro
                          let assump_379 := assump_376 assump_434
                          apply False.elim assump_379
                    case inr assump_356 =>
                      cases assump_356
                      case intro assump_383 assump_384 =>
                        cases assump_354
                        case intro assump_389 assump_390 =>
                          cases assump_390
                          case inl assump_393 =>
                            apply Or.inl
                            intro assump_397
                            have assump_435 : True := by
                              apply True.intro
                            let assump_400 := assump_397 assump_435
                            apply False.elim assump_400
                          case inr assump_394 =>
                            apply Or.inl
                            intro assump_406
                            have assump_436 : True := by
                              apply True.intro
                            let assump_409 := assump_406 assump_436
                            apply False.elim assump_409


variable (p2 p5 p1 p7 p0 p4 p6 : Prop)
theorem file69_117324 : (((((p6 → p7) → False) ∨ ((p2 ∨ p2) → (False → False))) → False) → ((((p5 → p0) → (p5 → True)) ∧ ((p4 ∨ False) ∧ (p7 ∧ p2))) → (((p1 → p2) → (p6 → True)) ∨ ((p5 ∨ p6) ∨ (p0 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          apply Or.inl
          intro assump_21
          intro assump_22
          apply True.intro
      case inr assump_10 =>
        apply False.elim assump_10


variable (p6 p3 : Prop)
theorem file69_117979 : ((((((True ∨ p6) ∨ (p3 ∨ p3)) → False) → False) → False) → False) := by
  intro assump_12
  have assump_26 : ((((True ∨ p6) ∨ (p3 ∨ p3)) → False) → False) := by
    intro assump_16
    have assump_27 : ((True ∨ p6) ∨ (p3 ∨ p3)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_19 := assump_16 assump_27
    apply False.elim assump_19
  let assump_15 := assump_12 assump_26
  apply False.elim assump_15


variable (p1 p7 p4 p3 : Prop)
theorem file69_118468 : (((((p1 → False) → (False ∨ True)) ∨ ((p4 ∨ True) ∨ (p7 ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p1 → False) → (False ∨ True)) ∨ ((p4 ∨ True) ∨ (p7 ∨ p3))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p1 p4 : Prop)
theorem file69_118850 : ((((((p1 ∧ p4) → (p7 → p7)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p1 ∧ p4) → (p7 → p7)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p1 ∧ p4) → (p7 → p7)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        exact assump_10
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p4 p0 p3 p5 p6 : Prop)
theorem file69_119395 : (((((p5 → False) ∨ (p0 → p3)) → ((True ∨ p6) → (p4 ∨ True))) → False) → ((((False → False) → (True → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_31 : (((p5 → False) ∨ (p0 → p3)) → ((True ∨ p6) → (p4 ∨ True))) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      cases assump_8
      case inl assump_14 =>
        apply Or.inr
        apply True.intro
      case inr assump_15 =>
        apply Or.inr
        apply True.intro
    case inr assump_11 =>
      cases assump_8
      case inl assump_22 =>
        apply Or.inr
        apply True.intro
      case inr assump_23 =>
        apply Or.inr
        apply True.intro
  let assump_7 := assump_1 assump_31
  apply False.elim assump_7


variable (p3 p1 p5 p0 p2 p6 p4 : Prop)
theorem file69_120222 : (((((True → False) ∧ (p0 ∨ p5)) ∧ ((False → False) → False)) → (((p4 ∧ p4) ∨ (p3 ∧ p2)) ∨ ((p1 → p5) → (p1 → p0)))) ∨ ((((True → False) → (p6 ∧ p2)) ∧ ((p5 ∧ False) → False)) → (((False → False) ∨ (p0 → False)) ∨ ((p5 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply Or.inr
        intro assump_14
        intro assump_15
        exact assump_8
      case inr assump_9 =>
        apply Or.inr
        intro assump_24
        intro assump_25
        have assump_40 : (False → False) := by
          intro assump_34
          apply False.elim assump_34
        let assump_33 := assump_3 assump_40
        apply False.elim assump_33


variable (p6 p7 p3 p1 p0 p5 p4 : Prop)
theorem file69_121093 : ((((((p5 → False) → False) ∧ ((p4 ∧ True) ∧ (p7 → False))) → (((p3 → False) ∨ (p4 → p3)) → False)) ∧ ((((p6 ∨ p0) ∨ (p1 ∨ False)) → False) ∧ (((p7 ∧ p1) → (False ∨ p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((p7 ∧ p1) → (False ∨ p1)) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply Or.inr
          exact assump_15
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p2 p0 p5 p1 p6 p4 : Prop)
theorem file69_121741 : ((((((p4 ∨ p5) ∧ (p5 ∨ p1)) → False) ∧ (((True ∧ False) ∧ (p6 ∨ True)) ∧ ((False → False) → False))) ∧ ((((p2 → p5) → (p2 → p6)) → False) ∧ (((p0 ∧ p2) → (p1 → False)) ∧ ((False → False) ∨ (p0 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p5 p4 p6 : Prop)
theorem file69_122368 : ((((((p4 ∧ False) ∧ (True → False)) ∨ ((p5 ∧ False) ∧ (p6 ∨ False))) → False) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p4 ∧ False) ∧ (True → False)) ∨ ((p5 ∧ False) ∧ (p6 ∨ False))) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply False.elim assump_19
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p5 p1 p2 : Prop)
theorem file69_123117 : (((((p5 ∨ False) ∨ (p1 → p1)) ∨ ((False ∧ False) ∨ (True ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p5 ∨ False) ∨ (p1 → p1)) ∨ ((False ∧ False) ∨ (True ∨ p2))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p2 p1 p0 p6 p3 p7 : Prop)
theorem file69_123511 : (((((p4 ∧ p4) → False) ∨ ((p1 ∨ True) → False)) ∧ (((p4 → p4) ∧ (p4 ∧ p3)) ∨ ((p2 → True) → False))) → ((((p7 ∨ False) ∨ (p3 → p0)) ∨ ((p2 ∨ True) ∧ (p6 → False))) → (((p3 → False) ∨ (p0 → p1)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_1
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_17
              case inl assump_22 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case intro assump_28 assump_29 =>
                    have assump_554 : (p4 ∧ p4) := by
                      apply And.intro
                      exact assump_28
                      exact assump_28
                    let assump_38 := assump_18 assump_554
                    apply False.elim assump_38
              case inr assump_23 =>
                have assump_555 : (p2 → True) := by
                  intro assump_45
                  apply True.intro
                let assump_44 := assump_23 assump_555
                apply False.elim assump_44
            case inr assump_19 =>
              cases assump_17
              case inl assump_51 =>
                cases assump_51
                case intro assump_53 assump_54 =>
                  cases assump_54
                  case intro assump_57 assump_58 =>
                    have assump_556 : (p1 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_67 := assump_19 assump_556
                    apply False.elim assump_67
              case inr assump_52 =>
                have assump_557 : (p2 → True) := by
                  intro assump_74
                  apply True.intro
                let assump_73 := assump_52 assump_557
                apply False.elim assump_73
        case inr assump_13 =>
          apply False.elim assump_13
      case inr assump_11 =>
        cases assump_1
        case intro assump_82 assump_83 =>
          cases assump_82
          case inl assump_84 =>
            cases assump_83
            case inl assump_88 =>
              cases assump_88
              case intro assump_90 assump_91 =>
                cases assump_91
                case intro assump_94 assump_95 =>
                  have assump_558 : (p4 ∧ p4) := by
                    apply And.intro
                    exact assump_94
                    exact assump_94
                  let assump_104 := assump_84 assump_558
                  apply False.elim assump_104
            case inr assump_89 =>
              have assump_559 : (p2 → True) := by
                intro assump_111
                apply True.intro
              let assump_110 := assump_89 assump_559
              apply False.elim assump_110
          case inr assump_85 =>
            cases assump_83
            case inl assump_117 =>
              cases assump_117
              case intro assump_119 assump_120 =>
                cases assump_120
                case intro assump_123 assump_124 =>
                  have assump_560 : (p1 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_133 := assump_85 assump_560
                  apply False.elim assump_133
            case inr assump_118 =>
              have assump_561 : (p2 → True) := by
                intro assump_140
                apply True.intro
              let assump_139 := assump_118 assump_561
              apply False.elim assump_139
    case inr assump_9 =>
      cases assump_9
      case intro assump_144 assump_145 =>
        cases assump_144
        case inl assump_146 =>
          cases assump_1
          case intro assump_152 assump_153 =>
            cases assump_152
            case inl assump_154 =>
              cases assump_153
              case inl assump_158 =>
                cases assump_158
                case intro assump_160 assump_161 =>
                  cases assump_161
                  case intro assump_164 assump_165 =>
                    have assump_562 : (p4 ∧ p4) := by
                      apply And.intro
                      exact assump_164
                      exact assump_164
                    let assump_174 := assump_154 assump_562
                    apply False.elim assump_174
              case inr assump_159 =>
                have assump_563 : (p2 → True) := by
                  intro assump_181
                  apply True.intro
                let assump_180 := assump_159 assump_563
                apply False.elim assump_180
            case inr assump_155 =>
              cases assump_153
              case inl assump_187 =>
                cases assump_187
                case intro assump_189 assump_190 =>
                  cases assump_190
                  case intro assump_193 assump_194 =>
                    have assump_564 : (p1 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_203 := assump_155 assump_564
                    apply False.elim assump_203
              case inr assump_188 =>
                have assump_565 : (p2 → True) := by
                  intro assump_210
                  apply True.intro
                let assump_209 := assump_188 assump_565
                apply False.elim assump_209
        case inr assump_147 =>
          cases assump_1
          case intro assump_218 assump_219 =>
            cases assump_218
            case inl assump_220 =>
              cases assump_219
              case inl assump_224 =>
                cases assump_224
                case intro assump_226 assump_227 =>
                  cases assump_227
                  case intro assump_230 assump_231 =>
                    have assump_566 : (p4 ∧ p4) := by
                      apply And.intro
                      exact assump_230
                      exact assump_230
                    let assump_240 := assump_220 assump_566
                    apply False.elim assump_240
              case inr assump_225 =>
                have assump_567 : (p2 → True) := by
                  intro assump_247
                  apply True.intro
                let assump_246 := assump_225 assump_567
                apply False.elim assump_246
            case inr assump_221 =>
              cases assump_219
              case inl assump_253 =>
                cases assump_253
                case intro assump_255 assump_256 =>
                  cases assump_256
                  case intro assump_259 assump_260 =>
                    have assump_568 : (p1 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_269 := assump_221 assump_568
                    apply False.elim assump_269
              case inr assump_254 =>
                have assump_569 : (p2 → True) := by
                  intro assump_276
                  apply True.intro
                let assump_275 := assump_254 assump_569
                apply False.elim assump_275
  case inr assump_5 =>
    cases assump_2
    case inl assump_282 =>
      cases assump_282
      case inl assump_284 =>
        cases assump_284
        case inl assump_286 =>
          cases assump_1
          case intro assump_290 assump_291 =>
            cases assump_290
            case inl assump_292 =>
              cases assump_291
              case inl assump_296 =>
                cases assump_296
                case intro assump_298 assump_299 =>
                  cases assump_299
                  case intro assump_302 assump_303 =>
                    have assump_570 : (p4 ∧ p4) := by
                      apply And.intro
                      exact assump_302
                      exact assump_302
                    let assump_312 := assump_292 assump_570
                    apply False.elim assump_312
              case inr assump_297 =>
                have assump_571 : (p2 → True) := by
                  intro assump_319
                  apply True.intro
                let assump_318 := assump_297 assump_571
                apply False.elim assump_318
            case inr assump_293 =>
              cases assump_291
              case inl assump_325 =>
                cases assump_325
                case intro assump_327 assump_328 =>
                  cases assump_328
                  case intro assump_331 assump_332 =>
                    have assump_572 : (p1 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_341 := assump_293 assump_572
                    apply False.elim assump_341
              case inr assump_326 =>
                have assump_573 : (p2 → True) := by
                  intro assump_348
                  apply True.intro
                let assump_347 := assump_326 assump_573
                apply False.elim assump_347
        case inr assump_287 =>
          apply False.elim assump_287
      case inr assump_285 =>
        cases assump_1
        case intro assump_356 assump_357 =>
          cases assump_356
          case inl assump_358 =>
            cases assump_357
            case inl assump_362 =>
              cases assump_362
              case intro assump_364 assump_365 =>
                cases assump_365
                case intro assump_368 assump_369 =>
                  have assump_574 : (p4 ∧ p4) := by
                    apply And.intro
                    exact assump_368
                    exact assump_368
                  let assump_378 := assump_358 assump_574
                  apply False.elim assump_378
            case inr assump_363 =>
              have assump_575 : (p2 → True) := by
                intro assump_385
                apply True.intro
              let assump_384 := assump_363 assump_575
              apply False.elim assump_384
          case inr assump_359 =>
            cases assump_357
            case inl assump_391 =>
              cases assump_391
              case intro assump_393 assump_394 =>
                cases assump_394
                case intro assump_397 assump_398 =>
                  have assump_576 : (p1 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_407 := assump_359 assump_576
                  apply False.elim assump_407
            case inr assump_392 =>
              have assump_577 : (p2 → True) := by
                intro assump_414
                apply True.intro
              let assump_413 := assump_392 assump_577
              apply False.elim assump_413
    case inr assump_283 =>
      cases assump_283
      case intro assump_418 assump_419 =>
        cases assump_418
        case inl assump_420 =>
          cases assump_1
          case intro assump_426 assump_427 =>
            cases assump_426
            case inl assump_428 =>
              cases assump_427
              case inl assump_432 =>
                cases assump_432
                case intro assump_434 assump_435 =>
                  cases assump_435
                  case intro assump_438 assump_439 =>
                    have assump_578 : (p4 ∧ p4) := by
                      apply And.intro
                      exact assump_438
                      exact assump_438
                    let assump_448 := assump_428 assump_578
                    apply False.elim assump_448
              case inr assump_433 =>
                have assump_579 : (p2 → True) := by
                  intro assump_455
                  apply True.intro
                let assump_454 := assump_433 assump_579
                apply False.elim assump_454
            case inr assump_429 =>
              cases assump_427
              case inl assump_461 =>
                cases assump_461
                case intro assump_463 assump_464 =>
                  cases assump_464
                  case intro assump_467 assump_468 =>
                    have assump_580 : (p1 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_477 := assump_429 assump_580
                    apply False.elim assump_477
              case inr assump_462 =>
                have assump_581 : (p2 → True) := by
                  intro assump_484
                  apply True.intro
                let assump_483 := assump_462 assump_581
                apply False.elim assump_483
        case inr assump_421 =>
          cases assump_1
          case intro assump_492 assump_493 =>
            cases assump_492
            case inl assump_494 =>
              cases assump_493
              case inl assump_498 =>
                cases assump_498
                case intro assump_500 assump_501 =>
                  cases assump_501
                  case intro assump_504 assump_505 =>
                    have assump_582 : (p4 ∧ p4) := by
                      apply And.intro
                      exact assump_504
                      exact assump_504
                    let assump_514 := assump_494 assump_582
                    apply False.elim assump_514
              case inr assump_499 =>
                have assump_583 : (p2 → True) := by
                  intro assump_521
                  apply True.intro
                let assump_520 := assump_499 assump_583
                apply False.elim assump_520
            case inr assump_495 =>
              cases assump_493
              case inl assump_527 =>
                cases assump_527
                case intro assump_529 assump_530 =>
                  cases assump_530
                  case intro assump_533 assump_534 =>
                    have assump_584 : (p1 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_543 := assump_495 assump_584
                    apply False.elim assump_543
              case inr assump_528 =>
                have assump_585 : (p2 → True) := by
                  intro assump_550
                  apply True.intro
                let assump_549 := assump_528 assump_585
                apply False.elim assump_549


variable (p2 p7 p5 p0 : Prop)
theorem file69_138023 : (((((False ∨ p2) ∧ (p0 ∨ p7)) ∨ ((False ∧ p5) → False)) → False) → False) := by
  intro assump_13
  have assump_25 : (((False ∨ p2) ∧ (p0 ∨ p7)) ∨ ((False ∧ p5) → False)) := by
    apply Or.inr
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      apply False.elim assump_18
  let assump_16 := assump_13 assump_25
  apply False.elim assump_16


