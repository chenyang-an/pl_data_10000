variable (p1 p6 p7 p3 p2 p4 : Prop)
theorem file81_44 : (((((p3 → p4) ∨ (p1 ∧ p6)) → ((p7 → p2) ∨ (False ∨ p6))) ∧ (((p7 → False) ∧ (p7 → p2)) ∧ ((p3 ∧ p1) ∧ (False ∧ p1)))) → False) := by
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
            cases assump_15
            case intro assump_22 assump_23 =>
              apply False.elim assump_22


variable (p1 p2 p4 p6 p3 p7 p0 p5 : Prop)
theorem file81_675 : (((((p0 ∧ p2) ∧ (p5 → p3)) ∨ ((p5 → p0) → False)) → (((False ∧ p7) ∧ (p2 ∨ p2)) → False)) ∨ ((((False → True) → (p0 ∨ p5)) ∧ ((False ∧ p1) → False)) ∧ (((p1 ∨ p4) ∧ (p5 ∧ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p2 : Prop)
theorem file81_1100 : (((((p2 ∨ True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((p2 ∨ True) → False) → False) := by
    intro assump_5
    have assump_16 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p2 p0 p4 : Prop)
theorem file81_1520 : ((((((True ∧ p4) ∧ (p7 ∧ False)) ∧ ((p0 ∧ True) → False)) ∨ (((p2 → False) ∧ (True → False)) → ((p0 → p7) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True ∧ p4) ∧ (p7 ∧ False)) ∧ ((p0 ∧ True) → False)) ∨ (((p2 → False) ∧ (True → False)) → ((p0 → p7) → False))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_23 : True := by
        apply True.intro
      let assump_15 := assump_10 assump_23
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p2 p4 p1 p5 p6 : Prop)
theorem file81_2189 : ((((((False ∧ p1) → (p7 → False)) → ((p1 ∧ False) ∧ (p2 → p6))) ∧ (((p7 → False) → (p2 ∧ True)) → False)) ∧ ((((p4 → p1) → False) → ((p7 → p6) → (False → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_21 : (((p4 → p1) → False) → ((p7 → p6) → (False → p5))) := by
        intro assump_13
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      let assump_12 := assump_3 assump_21
      apply False.elim assump_12


variable (p3 p7 p6 p4 p5 p0 p1 : Prop)
theorem file81_2822 : (((((False → False) → False) ∧ ((False ∧ True) → (p6 ∨ p0))) → False) ∨ ((((p6 ∨ p4) ∧ (p7 ∧ p7)) ∨ ((p3 → p1) ∧ (p7 ∨ p5))) ∧ (((p4 → False) → False) ∧ ((True ∧ p6) ∧ (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (False → False) := by
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p2 p7 p1 p5 p3 p0 p4 : Prop)
theorem file81_3326 : (((((True → p0) ∨ (p1 ∧ True)) ∧ ((True → False) → False)) ∧ (((p0 ∨ p2) → (p0 → False)) ∧ ((p3 → False) ∧ (True ∧ p0)))) → ((((p1 → p5) ∨ (p7 ∨ p4)) ∨ ((True ∨ p0) ∧ (p1 → False))) ∨ (((p7 → False) ∧ (False → False)) ∧ ((p4 → p4) → (p0 ∨ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              intro assump_26
              have assump_70 : (p0 ∨ p2) := by
                apply Or.inl
                exact assump_21
              let assump_32 := assump_12 assump_70
              have assump_71 : p0 := by
                exact assump_21
              let assump_33 := assump_32 assump_71
              apply False.elim assump_33
      case inr assump_7 =>
        cases assump_7
        case intro assump_37 assump_38 =>
          cases assump_3
          case intro assump_45 assump_46 =>
            cases assump_46
            case intro assump_49 assump_50 =>
              cases assump_50
              case intro assump_53 assump_54 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                intro assump_59
                have assump_72 : (p0 ∨ p2) := by
                  apply Or.inl
                  exact assump_54
                let assump_65 := assump_45 assump_72
                have assump_73 : p0 := by
                  exact assump_54
                let assump_66 := assump_65 assump_73
                apply False.elim assump_66


variable (p7 p1 p6 p5 p2 p4 p3 : Prop)
theorem file81_5227 : (((((p4 ∨ p7) → (p7 ∨ p4)) → False) → False) ∨ ((((p1 ∨ p7) ∨ (p4 ∧ p4)) ∨ ((p3 ∧ p5) ∧ (p5 → False))) → (((p7 ∨ False) ∧ (p5 ∧ p6)) ∨ ((p3 ∧ p6) ∧ (p2 → False))))) := by
  apply Or.inl
  intro assump_5
  have assump_19 : ((p4 ∨ p7) → (p7 ∨ p4)) := by
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply Or.inr
      exact assump_10
    case inr assump_11 =>
      apply Or.inl
      exact assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p1 p6 p4 p0 p7 : Prop)
theorem file81_5773 : (((((p1 ∨ p0) ∧ (p6 → p4)) → False) ∧ (((p0 ∧ p7) → (False ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p0 ∧ p7) → (False ∨ True)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p1 p3 p4 : Prop)
theorem file81_6238 : ((((((True ∧ p4) → False) ∧ ((p4 → False) → False)) → (((p3 → p3) ∨ (True ∧ p1)) ∨ ((p1 ∧ p4) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True ∧ p4) → False) ∧ ((p4 → False) → False)) → (((p3 → p3) ∨ (True ∧ p1)) ∨ ((p1 ∧ p4) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      exact assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p7 p2 p1 p6 p0 p5 : Prop)
theorem file81_6796 : (((((p6 ∨ p6) ∨ (p3 ∨ False)) ∨ ((p1 → True) → (p7 → False))) ∧ (((p1 ∨ p2) ∧ (p2 → p0)) ∧ ((p6 ∨ p1) ∧ (True → False)))) → ((((p0 → False) ∨ (p1 ∧ p1)) ∨ ((p2 ∨ p5) → (True → False))) ∧ (((p7 → False) → False) → ((p2 → False) → (p6 ∨ p5))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_14
              case inl assump_16 =>
                cases assump_13
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case inl assump_24 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_30
                    have assump_496 : True := by
                      apply True.intro
                    let assump_34 := assump_23 assump_496
                    apply False.elim assump_34
                  case inr assump_25 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_42
                    have assump_497 : True := by
                      apply True.intro
                    let assump_46 := assump_23 assump_497
                    apply False.elim assump_46
              case inr assump_17 =>
                cases assump_13
                case intro assump_54 assump_55 =>
                  cases assump_54
                  case inl assump_56 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_62
                    have assump_498 : True := by
                      apply True.intro
                    let assump_66 := assump_55 assump_498
                    apply False.elim assump_66
                  case inr assump_57 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_74
                    have assump_499 : True := by
                      apply True.intro
                    let assump_78 := assump_55 assump_499
                    apply False.elim assump_78
        case inr assump_9 =>
          cases assump_3
          case intro assump_84 assump_85 =>
            cases assump_84
            case intro assump_86 assump_87 =>
              cases assump_86
              case inl assump_88 =>
                cases assump_85
                case intro assump_94 assump_95 =>
                  cases assump_94
                  case inl assump_96 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_102
                    have assump_500 : True := by
                      apply True.intro
                    let assump_106 := assump_95 assump_500
                    apply False.elim assump_106
                  case inr assump_97 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_114
                    have assump_501 : True := by
                      apply True.intro
                    let assump_118 := assump_95 assump_501
                    apply False.elim assump_118
              case inr assump_89 =>
                cases assump_85
                case intro assump_126 assump_127 =>
                  cases assump_126
                  case inl assump_128 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_134
                    have assump_502 : True := by
                      apply True.intro
                    let assump_138 := assump_127 assump_502
                    apply False.elim assump_138
                  case inr assump_129 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_146
                    have assump_503 : True := by
                      apply True.intro
                    let assump_150 := assump_127 assump_503
                    apply False.elim assump_150
      case inr assump_7 =>
        cases assump_7
        case inl assump_154 =>
          cases assump_3
          case intro assump_158 assump_159 =>
            cases assump_158
            case intro assump_160 assump_161 =>
              cases assump_160
              case inl assump_162 =>
                cases assump_159
                case intro assump_168 assump_169 =>
                  cases assump_168
                  case inl assump_170 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_176
                    have assump_504 : True := by
                      apply True.intro
                    let assump_180 := assump_169 assump_504
                    apply False.elim assump_180
                  case inr assump_171 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_188
                    have assump_505 : True := by
                      apply True.intro
                    let assump_192 := assump_169 assump_505
                    apply False.elim assump_192
              case inr assump_163 =>
                cases assump_159
                case intro assump_200 assump_201 =>
                  cases assump_200
                  case inl assump_202 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_208
                    have assump_506 : True := by
                      apply True.intro
                    let assump_212 := assump_201 assump_506
                    apply False.elim assump_212
                  case inr assump_203 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_220
                    have assump_507 : True := by
                      apply True.intro
                    let assump_224 := assump_201 assump_507
                    apply False.elim assump_224
        case inr assump_155 =>
          apply False.elim assump_155
    case inr assump_5 =>
      cases assump_3
      case intro assump_232 assump_233 =>
        cases assump_232
        case intro assump_234 assump_235 =>
          cases assump_234
          case inl assump_236 =>
            cases assump_233
            case intro assump_242 assump_243 =>
              cases assump_242
              case inl assump_244 =>
                apply Or.inl
                apply Or.inl
                intro assump_250
                have assump_508 : True := by
                  apply True.intro
                let assump_254 := assump_243 assump_508
                apply False.elim assump_254
              case inr assump_245 =>
                apply Or.inl
                apply Or.inl
                intro assump_262
                have assump_509 : True := by
                  apply True.intro
                let assump_266 := assump_243 assump_509
                apply False.elim assump_266
          case inr assump_237 =>
            cases assump_233
            case intro assump_274 assump_275 =>
              cases assump_274
              case inl assump_276 =>
                apply Or.inl
                apply Or.inl
                intro assump_282
                have assump_510 : True := by
                  apply True.intro
                let assump_286 := assump_275 assump_510
                apply False.elim assump_286
              case inr assump_277 =>
                apply Or.inl
                apply Or.inl
                intro assump_294
                have assump_511 : True := by
                  apply True.intro
                let assump_298 := assump_275 assump_511
                apply False.elim assump_298
  intro assump_302
  intro assump_303
  cases assump_1
  case intro assump_308 assump_309 =>
    cases assump_308
    case inl assump_310 =>
      cases assump_310
      case inl assump_312 =>
        cases assump_312
        case inl assump_314 =>
          cases assump_309
          case intro assump_318 assump_319 =>
            cases assump_318
            case intro assump_320 assump_321 =>
              cases assump_320
              case inl assump_322 =>
                cases assump_319
                case intro assump_328 assump_329 =>
                  cases assump_328
                  case inl assump_330 =>
                    apply Or.inl
                    exact assump_330
                  case inr assump_331 =>
                    apply Or.inl
                    exact assump_314
              case inr assump_323 =>
                cases assump_319
                case intro assump_344 assump_345 =>
                  cases assump_344
                  case inl assump_346 =>
                    apply Or.inl
                    exact assump_346
                  case inr assump_347 =>
                    apply Or.inl
                    exact assump_314
        case inr assump_315 =>
          cases assump_309
          case intro assump_358 assump_359 =>
            cases assump_358
            case intro assump_360 assump_361 =>
              cases assump_360
              case inl assump_362 =>
                cases assump_359
                case intro assump_368 assump_369 =>
                  cases assump_368
                  case inl assump_370 =>
                    apply Or.inl
                    exact assump_370
                  case inr assump_371 =>
                    apply Or.inl
                    exact assump_315
              case inr assump_363 =>
                cases assump_359
                case intro assump_384 assump_385 =>
                  cases assump_384
                  case inl assump_386 =>
                    apply Or.inl
                    exact assump_386
                  case inr assump_387 =>
                    apply Or.inl
                    exact assump_315
      case inr assump_313 =>
        cases assump_313
        case inl assump_396 =>
          cases assump_309
          case intro assump_400 assump_401 =>
            cases assump_400
            case intro assump_402 assump_403 =>
              cases assump_402
              case inl assump_404 =>
                cases assump_401
                case intro assump_410 assump_411 =>
                  cases assump_410
                  case inl assump_412 =>
                    apply Or.inl
                    exact assump_412
                  case inr assump_413 =>
                    have assump_512 : True := by
                      apply True.intro
                    let assump_422 := assump_411 assump_512
                    apply False.elim assump_422
              case inr assump_405 =>
                cases assump_401
                case intro assump_430 assump_431 =>
                  cases assump_430
                  case inl assump_432 =>
                    apply Or.inl
                    exact assump_432
                  case inr assump_433 =>
                    have assump_513 : True := by
                      apply True.intro
                    let assump_442 := assump_431 assump_513
                    apply False.elim assump_442
        case inr assump_397 =>
          apply False.elim assump_397
    case inr assump_311 =>
      cases assump_309
      case intro assump_450 assump_451 =>
        cases assump_450
        case intro assump_452 assump_453 =>
          cases assump_452
          case inl assump_454 =>
            cases assump_451
            case intro assump_460 assump_461 =>
              cases assump_460
              case inl assump_462 =>
                apply Or.inl
                exact assump_462
              case inr assump_463 =>
                have assump_514 : True := by
                  apply True.intro
                let assump_472 := assump_461 assump_514
                apply False.elim assump_472
          case inr assump_455 =>
            cases assump_451
            case intro assump_480 assump_481 =>
              cases assump_480
              case inl assump_482 =>
                apply Or.inl
                exact assump_482
              case inr assump_483 =>
                have assump_515 : True := by
                  apply True.intro
                let assump_492 := assump_481 assump_515
                apply False.elim assump_492


variable (p7 p5 p4 p1 p0 p6 p3 : Prop)
theorem file81_19326 : (((((False ∨ p1) ∨ (p5 → False)) → ((True ∧ p4) → False)) → (((p1 → True) ∨ (p3 → False)) ∨ ((True → False) ∧ (False ∧ p6)))) ∨ ((((p0 ∧ p7) → (p7 → False)) ∧ ((p1 → True) → False)) ∨ (((p3 → p6) → (p1 ∨ p6)) → ((p0 → p4) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p6 p0 p3 p4 : Prop)
theorem file81_19718 : (((((p3 ∧ p6) → (p3 → p4)) → False) ∧ (((p4 ∧ p0) ∨ (p3 → False)) ∧ ((p3 ∧ p6) ∧ (p0 ∧ False)))) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_16
          case intro assump_25 assump_26 =>
            cases assump_25
            case intro assump_27 assump_28 =>
              cases assump_26
              case intro assump_33 assump_34 =>
                apply False.elim assump_34
      case inr assump_18 =>
        cases assump_16
        case intro assump_41 assump_42 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            cases assump_42
            case intro assump_49 assump_50 =>
              apply False.elim assump_50


variable (p0 p7 p2 p4 p3 p6 p1 : Prop)
theorem file81_20683 : (((((p7 ∧ p3) → (p2 → False)) → False) → (((p1 → False) ∧ (False ∧ p6)) → False)) ∨ ((((True → False) → (p2 → False)) ∧ ((p3 ∧ p4) → (True ∨ p1))) ∧ (((p0 ∨ True) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p6 p4 p0 p7 p3 : Prop)
theorem file81_21116 : ((((((p4 ∨ p4) ∧ (False ∧ p3)) ∨ ((p3 ∧ False) → False)) ∨ (((p3 ∧ True) ∧ (p7 → True)) ∧ ((p7 ∧ p0) ∧ (p0 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p4 ∨ p4) ∧ (False ∧ p3)) ∨ ((p3 ∧ False) → False)) ∨ (((p3 ∧ True) ∧ (p7 → True)) ∧ ((p7 ∧ p0) ∧ (p0 ∨ p6)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p4 p6 p2 p0 p7 : Prop)
theorem file81_21677 : (((((False → False) → (p7 → False)) → ((p7 → False) ∨ (p1 ∧ True))) ∧ (((True → False) → False) → ((False → False) → (p6 → False)))) → ((((p6 → p6) → (p4 ∨ p4)) → ((False → True) ∧ (p0 → True))) ∨ (((p0 ∧ p2) ∧ (p0 → p4)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply And.intro
    intro assump_9
    apply True.intro
    intro assump_10
    apply True.intro


variable (p6 p4 p3 p7 p1 p2 p0 : Prop)
theorem file81_22184 : (((((p3 ∧ p0) ∧ (p6 ∧ p4)) ∧ ((p3 ∧ p3) → (p6 → p2))) → (((p7 ∨ True) ∧ (p4 → False)) → False)) ∨ ((((p3 ∧ p6) → (True ∧ True)) → False) → (((p4 ∧ p0) ∨ (p4 ∧ p1)) ∧ ((p4 ∨ p4) ∧ (False → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_14
            case intro assump_21 assump_22 =>
              have assump_73 : p4 := by
                exact assump_22
              let assump_36 := assump_4 assump_73
              apply False.elim assump_36
    case inr assump_6 =>
      cases assump_1
      case intro assump_44 assump_45 =>
        cases assump_44
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_47
            case intro assump_54 assump_55 =>
              have assump_74 : p4 := by
                exact assump_55
              let assump_69 := assump_4 assump_74
              apply False.elim assump_69


variable (p2 p3 p0 p1 p4 p6 p5 : Prop)
theorem file81_23489 : ((((((True ∨ p3) → (p3 ∧ p3)) ∧ ((True ∧ p4) ∧ (True ∧ True))) ∧ (((p6 → False) ∨ (p6 ∧ False)) ∨ ((p1 ∨ True) ∧ (True → p0)))) ∧ ((((p5 → False) ∧ (True → False)) → ((p4 ∨ p5) → (p1 ∧ p1))) → (((True ∨ p2) ∨ (False → True)) → False))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_24
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            cases assump_28
            case intro assump_35 assump_36 =>
              cases assump_22
              case inl assump_41 =>
                cases assump_41
                case inl assump_43 =>
                  have assump_232 : (((p5 → False) ∧ (True → False)) → ((p4 ∨ p5) → (p1 ∧ p1))) := by
                    intro assump_50
                    intro assump_51
                    apply And.intro
                    cases assump_51
                    case inl assump_52 =>
                      cases assump_50
                      case intro assump_56 assump_57 =>
                        have assump_233 : True := by
                          apply True.intro
                        let assump_62 := assump_57 assump_233
                        apply False.elim assump_62
                    case inr assump_53 =>
                      cases assump_50
                      case intro assump_68 assump_69 =>
                        have assump_234 : True := by
                          apply True.intro
                        let assump_74 := assump_69 assump_234
                        apply False.elim assump_74
                    cases assump_51
                    case inl assump_78 =>
                      cases assump_50
                      case intro assump_82 assump_83 =>
                        have assump_235 : True := by
                          apply True.intro
                        let assump_88 := assump_83 assump_235
                        apply False.elim assump_88
                    case inr assump_79 =>
                      cases assump_50
                      case intro assump_94 assump_95 =>
                        have assump_236 : True := by
                          apply True.intro
                        let assump_100 := assump_95 assump_236
                        apply False.elim assump_100
                  let assump_49 := assump_20 assump_232
                  have assump_237 : ((True ∨ p2) ∨ (False → True)) := by
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_104 := assump_49 assump_237
                  apply False.elim assump_104
                case inr assump_44 =>
                  cases assump_44
                  case intro assump_108 assump_109 =>
                    apply False.elim assump_109
              case inr assump_42 =>
                cases assump_42
                case intro assump_114 assump_115 =>
                  cases assump_114
                  case inl assump_116 =>
                    have assump_238 : (((p5 → False) ∧ (True → False)) → ((p4 ∨ p5) → (p1 ∧ p1))) := by
                      intro assump_125
                      intro assump_126
                      apply And.intro
                      cases assump_126
                      case inl assump_127 =>
                        cases assump_125
                        case intro assump_131 assump_132 =>
                          exact assump_116
                      case inr assump_128 =>
                        cases assump_125
                        case intro assump_139 assump_140 =>
                          exact assump_116
                      cases assump_126
                      case inl assump_145 =>
                        cases assump_125
                        case intro assump_149 assump_150 =>
                          exact assump_116
                      case inr assump_146 =>
                        cases assump_125
                        case intro assump_157 assump_158 =>
                          exact assump_116
                    let assump_124 := assump_20 assump_238
                    have assump_239 : ((True ∨ p2) ∨ (False → True)) := by
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    let assump_163 := assump_124 assump_239
                    apply False.elim assump_163
                  case inr assump_117 =>
                    have assump_240 : (((p5 → False) ∧ (True → False)) → ((p4 ∨ p5) → (p1 ∧ p1))) := by
                      intro assump_174
                      intro assump_175
                      apply And.intro
                      cases assump_175
                      case inl assump_176 =>
                        cases assump_174
                        case intro assump_180 assump_181 =>
                          have assump_241 : True := by
                            apply True.intro
                          let assump_186 := assump_181 assump_241
                          apply False.elim assump_186
                      case inr assump_177 =>
                        cases assump_174
                        case intro assump_192 assump_193 =>
                          have assump_242 : True := by
                            apply True.intro
                          let assump_198 := assump_193 assump_242
                          apply False.elim assump_198
                      cases assump_175
                      case inl assump_202 =>
                        cases assump_174
                        case intro assump_206 assump_207 =>
                          have assump_243 : True := by
                            apply True.intro
                          let assump_212 := assump_207 assump_243
                          apply False.elim assump_212
                      case inr assump_203 =>
                        cases assump_174
                        case intro assump_218 assump_219 =>
                          have assump_244 : True := by
                            apply True.intro
                          let assump_224 := assump_219 assump_244
                          apply False.elim assump_224
                    let assump_173 := assump_20 assump_240
                    have assump_245 : ((True ∨ p2) ∨ (False → True)) := by
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    let assump_228 := assump_173 assump_245
                    apply False.elim assump_228


variable (p2 p7 p1 p0 p5 p4 p6 p3 : Prop)
theorem file81_30272 : (((((p5 → False) ∧ (p3 → False)) ∧ ((p0 → True) ∧ (p4 → False))) ∨ (((p3 ∨ p3) → (p1 → True)) ∧ ((p1 → False) ∧ (p7 → False)))) → ((((p4 ∨ True) → (p5 → p7)) ∨ ((True ∧ p3) ∧ (p7 ∧ p0))) → (((p6 ∧ False) → (p2 → False)) ∨ ((p1 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_10
          case intro assump_17 assump_18 =>
            apply Or.inl
            intro assump_23
            intro assump_24
            cases assump_23
            case intro assump_27 assump_28 =>
              apply False.elim assump_28
    case inr assump_8 =>
      cases assump_8
      case intro assump_33 assump_34 =>
        cases assump_34
        case intro assump_37 assump_38 =>
          apply Or.inl
          intro assump_43
          intro assump_44
          cases assump_43
          case intro assump_47 assump_48 =>
            apply False.elim assump_48
  case inr assump_4 =>
    cases assump_4
    case intro assump_53 assump_54 =>
      cases assump_53
      case intro assump_55 assump_56 =>
        cases assump_54
        case intro assump_61 assump_62 =>
          cases assump_1
          case inl assump_67 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              cases assump_69
              case intro assump_71 assump_72 =>
                cases assump_70
                case intro assump_77 assump_78 =>
                  apply Or.inl
                  intro assump_83
                  intro assump_84
                  cases assump_83
                  case intro assump_87 assump_88 =>
                    apply False.elim assump_88
          case inr assump_68 =>
            cases assump_68
            case intro assump_93 assump_94 =>
              cases assump_94
              case intro assump_97 assump_98 =>
                apply Or.inl
                intro assump_103
                intro assump_104
                cases assump_103
                case intro assump_107 assump_108 =>
                  apply False.elim assump_108


variable (p2 p7 p0 : Prop)
theorem file81_32563 : (((((False → False) → False) → ((p0 → p2) → (p7 ∨ False))) → False) → False) := by
  intro assump_9
  have assump_29 : (((False → False) → False) → ((p0 → p2) → (p7 ∨ False))) := by
    intro assump_13
    intro assump_14
    have assump_30 : (False → False) := by
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_13 assump_30
    apply False.elim assump_19
  let assump_12 := assump_9 assump_29
  apply False.elim assump_12


variable (p3 p0 p4 p1 : Prop)
theorem file81_33076 : (((((False → False) ∨ (p4 → False)) ∨ ((p3 → False) ∨ (p0 ∧ p1))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → False) ∨ (p4 → False)) ∨ ((p3 → False) ∨ (p0 ∧ p1))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p1 p3 p0 p4 p6 : Prop)
theorem file81_33483 : (((((p4 ∧ p4) ∨ (p5 → True)) → ((p4 ∨ p0) → False)) → False) → ((((True → False) → False) ∨ ((p7 ∧ True) ∨ (p7 ∧ p1))) ∨ (((p6 → False) ∧ (True → p6)) → ((p0 → p3) → (p5 ∧ p5))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p2 p0 p6 p4 p1 p7 p3 : Prop)
theorem file81_33912 : (((((p7 ∧ p4) ∨ (p7 → p7)) ∨ ((False ∧ p7) → False)) → False) → ((((p2 ∧ p1) ∨ (p6 ∨ True)) ∨ ((p6 ∨ p2) ∧ (p0 ∨ p4))) → (((p1 → p0) ∨ (p6 → p2)) ∨ ((p1 → p1) ∨ (p6 → p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply Or.inl
        apply Or.inl
        intro assump_15
        have assump_114 : (((p7 ∧ p4) ∨ (p7 → p7)) ∨ ((False ∧ p7) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_20
          exact assump_20
        let assump_19 := assump_1 assump_114
        apply False.elim assump_19
    case inr assump_6 =>
      cases assump_6
      case inl assump_26 =>
        apply Or.inl
        apply Or.inl
        intro assump_32
        have assump_115 : (((p7 ∧ p4) ∨ (p7 → p7)) ∨ ((False ∧ p7) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_37
          exact assump_37
        let assump_36 := assump_1 assump_115
        apply False.elim assump_36
      case inr assump_27 =>
        apply Or.inl
        apply Or.inl
        intro assump_47
        have assump_116 : (((p7 ∧ p4) ∨ (p7 → p7)) ∨ ((False ∧ p7) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_52
          exact assump_52
        let assump_51 := assump_1 assump_116
        apply False.elim assump_51
  case inr assump_4 =>
    cases assump_4
    case intro assump_58 assump_59 =>
      cases assump_58
      case inl assump_60 =>
        cases assump_59
        case inl assump_64 =>
          apply Or.inl
          apply Or.inl
          intro assump_70
          exact assump_64
        case inr assump_65 =>
          apply Or.inl
          apply Or.inl
          intro assump_77
          have assump_117 : (((p7 ∧ p4) ∨ (p7 → p7)) ∨ ((False ∧ p7) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_82
            exact assump_82
          let assump_81 := assump_1 assump_117
          apply False.elim assump_81
      case inr assump_61 =>
        cases assump_59
        case inl assump_90 =>
          apply Or.inl
          apply Or.inl
          intro assump_96
          exact assump_90
        case inr assump_91 =>
          apply Or.inl
          apply Or.inl
          intro assump_103
          have assump_118 : (((p7 ∧ p4) ∨ (p7 → p7)) ∨ ((False ∧ p7) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_108
            exact assump_108
          let assump_107 := assump_1 assump_118
          apply False.elim assump_107


variable (p3 p2 p7 p1 p6 p5 : Prop)
theorem file81_36634 : (((((p5 ∧ p2) → (p6 ∧ p6)) ∧ ((p7 ∧ False) ∨ (False ∧ p3))) ∧ (((True ∨ p5) ∧ (p3 → p7)) → ((p7 ∨ False) → (p1 ∨ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_9 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          apply False.elim assump_16


variable (p0 p4 p3 p1 p6 p2 p7 : Prop)
theorem file81_37234 : (((((p2 ∧ p1) ∨ (p1 → p0)) → False) → (((p4 ∨ False) → (p7 → False)) → ((p6 ∧ p0) → False))) ∨ ((((p4 → False) → (p4 ∧ p3)) → ((p7 ∧ True) → (p6 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_21 : ((p2 ∧ p1) ∨ (p1 → p0)) := by
      apply Or.inr
      intro assump_15
      exact assump_5
    let assump_14 := assump_1 assump_21
    apply False.elim assump_14


variable (p0 p2 p5 p7 p4 : Prop)
theorem file81_37763 : ((((((p0 ∧ p7) → (p2 ∧ p5)) ∧ ((p4 ∨ p5) → False)) → (((p5 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p0 ∧ p7) → (p2 ∧ p5)) ∧ ((p4 ∨ p5) → False)) → (((p5 → False) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_33 : (p5 → False) := by
        intro assump_18
        have assump_34 : (p4 ∨ p5) := by
          apply Or.inr
          exact assump_18
        let assump_22 := assump_10 assump_34
        apply False.elim assump_22
      let assump_17 := assump_6 assump_33
      apply False.elim assump_17
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p2 p7 p3 p4 p6 p1 : Prop)
theorem file81_38531 : (((((True ∨ False) → False) ∧ ((p1 → True) → False)) → False) ∨ ((((p3 ∨ False) ∧ (p2 ∨ p7)) ∧ ((p6 ∨ p4) ∨ (p1 → False))) ∨ (((p4 ∨ p4) ∨ (p4 ∨ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (p1 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p1 p5 p0 p2 p4 p7 p6 : Prop)
theorem file81_38996 : ((((((p0 → True) → False) → ((p5 ∨ p1) → False)) → (((False ∧ p4) ∨ (p6 → False)) ∨ ((False ∧ p2) → (p2 → p4)))) ∧ ((((p1 → False) ∧ (p4 ∧ p7)) → ((False ∧ True) ∧ (False ∧ False))) ∧ (((p6 → False) → (False → p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_20 : ((p6 → False) → (False → p4)) := by
        intro assump_13
        intro assump_14
        apply False.elim assump_14
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12


variable (p4 p0 p6 p2 p5 p7 p1 : Prop)
theorem file81_39640 : (((((p6 ∨ p2) ∨ (p4 ∨ False)) ∧ ((p2 → False) → (p1 ∨ True))) ∧ (((p4 ∧ p7) ∨ (p0 ∧ False)) → ((p4 → p5) ∨ (p2 → False)))) → ((((p6 → False) ∧ (True → False)) → ((True ∧ p4) ∧ (False ∧ False))) ∨ (((p7 ∧ p7) ∧ (p0 ∨ p0)) ∨ ((p2 ∧ p1) ∧ (p1 → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          intro assump_16
          apply And.intro
          apply And.intro
          apply True.intro
          cases assump_16
          case intro assump_17 assump_18 =>
            have assump_121 : True := by
              apply True.intro
            let assump_23 := assump_18 assump_121
            apply False.elim assump_23
          apply And.intro
          cases assump_16
          case intro assump_27 assump_28 =>
            have assump_122 : True := by
              apply True.intro
            let assump_33 := assump_28 assump_122
            apply False.elim assump_33
          cases assump_16
          case intro assump_37 assump_38 =>
            have assump_123 : True := by
              apply True.intro
            let assump_43 := assump_38 assump_123
            apply False.elim assump_43
        case inr assump_9 =>
          apply Or.inl
          intro assump_53
          apply And.intro
          apply And.intro
          apply True.intro
          cases assump_53
          case intro assump_54 assump_55 =>
            have assump_124 : True := by
              apply True.intro
            let assump_60 := assump_55 assump_124
            apply False.elim assump_60
          apply And.intro
          cases assump_53
          case intro assump_64 assump_65 =>
            have assump_125 : True := by
              apply True.intro
            let assump_70 := assump_65 assump_125
            apply False.elim assump_70
          cases assump_53
          case intro assump_74 assump_75 =>
            have assump_126 : True := by
              apply True.intro
            let assump_80 := assump_75 assump_126
            apply False.elim assump_80
      case inr assump_7 =>
        cases assump_7
        case inl assump_84 =>
          apply Or.inl
          intro assump_92
          apply And.intro
          apply And.intro
          apply True.intro
          cases assump_92
          case intro assump_93 assump_94 =>
            exact assump_84
          apply And.intro
          cases assump_92
          case intro assump_99 assump_100 =>
            have assump_127 : True := by
              apply True.intro
            let assump_105 := assump_100 assump_127
            apply False.elim assump_105
          cases assump_92
          case intro assump_109 assump_110 =>
            have assump_128 : True := by
              apply True.intro
            let assump_115 := assump_110 assump_128
            apply False.elim assump_115
        case inr assump_85 =>
          apply False.elim assump_85


variable (p2 p5 p0 p7 p4 p6 p3 p1 : Prop)
theorem file81_42780 : ((((((p1 ∨ p7) ∨ (p0 ∧ p2)) → ((p5 ∨ True) → (p6 ∧ p7))) ∧ (((p1 → False) ∨ (False ∨ p7)) ∧ ((p4 → p5) ∨ (True → p2)))) ∧ ((((p3 → False) → (True → p2)) → ((p3 → False) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            have assump_76 : (((p3 → False) → (True → p2)) → ((p3 → False) → (False → False))) := by
              intro assump_21
              intro assump_22
              intro assump_23
              apply False.elim assump_23
            let assump_20 := assump_3 assump_76
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_77 : (((p3 → False) → (True → p2)) → ((p3 → False) → (False → False))) := by
              intro assump_34
              intro assump_35
              intro assump_36
              apply False.elim assump_36
            let assump_33 := assump_3 assump_77
            apply False.elim assump_33
        case inr assump_11 =>
          cases assump_11
          case inl assump_42 =>
            apply False.elim assump_42
          case inr assump_43 =>
            cases assump_9
            case inl assump_48 =>
              have assump_78 : (((p3 → False) → (True → p2)) → ((p3 → False) → (False → False))) := by
                intro assump_55
                intro assump_56
                intro assump_57
                apply False.elim assump_57
              let assump_54 := assump_3 assump_78
              apply False.elim assump_54
            case inr assump_49 =>
              have assump_79 : (((p3 → False) → (True → p2)) → ((p3 → False) → (False → False))) := by
                intro assump_68
                intro assump_69
                intro assump_70
                apply False.elim assump_70
              let assump_67 := assump_3 assump_79
              apply False.elim assump_67


variable (p5 p0 p3 p2 : Prop)
theorem file81_44930 : ((((((p3 → False) → (p5 ∨ True)) → False) → (((p0 → False) ∨ (p2 ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p3 → False) → (p5 ∨ True)) → False) → (((p0 → False) ∨ (p2 ∨ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_39 : ((p3 → False) → (p5 ∨ True)) := by
        intro assump_14
        apply Or.inr
        apply True.intro
      let assump_13 := assump_5 assump_39
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case inl assump_20 =>
        have assump_40 : ((p3 → False) → (p5 ∨ True)) := by
          intro assump_27
          apply Or.inr
          apply True.intro
        let assump_26 := assump_5 assump_40
        apply False.elim assump_26
      case inr assump_21 =>
        apply False.elim assump_21
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p1 p7 p2 p0 p3 : Prop)
theorem file81_45923 : (((((p7 ∧ True) ∧ (True ∧ False)) → False) ∨ (((p7 ∨ p0) → False) → False)) ∨ ((((True ∧ p0) ∨ (p3 ∨ p2)) ∧ ((p3 ∨ p3) ∨ (p1 → p1))) ∨ (((p2 → False) ∨ (True ∧ p0)) ∨ ((False ∧ p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply False.elim assump_11


variable (p6 p7 p0 p5 : Prop)
theorem file81_46425 : ((((((p7 ∧ p5) → (p6 → False)) → False) → (((p0 ∧ False) ∧ (p5 → True)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 ∧ p5) → (p6 → False)) → False) → (((p0 ∧ False) ∧ (p5 → True)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p5 p2 p4 p6 p3 p1 : Prop)
theorem file81_46969 : (((((p3 → True) → False) ∧ ((p0 ∧ p4) ∨ (True → False))) → False) ∨ ((((False ∨ p2) ∧ (p0 → p6)) ∨ ((p0 → False) ∨ (p6 ∧ True))) → (((p1 → False) ∧ (p5 → p2)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_27 : (p3 → True) := by
          intro assump_17
          apply True.intro
        let assump_16 := assump_2 assump_27
        apply False.elim assump_16
    case inr assump_7 =>
      have assump_28 : True := by
        apply True.intro
      let assump_23 := assump_7 assump_28
      apply False.elim assump_23


variable (p1 p0 p7 p4 p5 : Prop)
theorem file81_47722 : (((((p7 → p1) ∨ (p4 ∨ p0)) ∧ ((p0 ∨ p7) ∧ (True → False))) → False) ∨ ((((p5 ∨ p0) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_74 : True := by
            apply True.intro
          let assump_16 := assump_9 assump_74
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_75 : True := by
            apply True.intro
          let assump_24 := assump_9 assump_75
          apply False.elim assump_24
    case inr assump_5 =>
      cases assump_5
      case inl assump_28 =>
        cases assump_3
        case intro assump_32 assump_33 =>
          cases assump_32
          case inl assump_34 =>
            have assump_76 : True := by
              apply True.intro
            let assump_40 := assump_33 assump_76
            apply False.elim assump_40
          case inr assump_35 =>
            have assump_77 : True := by
              apply True.intro
            let assump_48 := assump_33 assump_77
            apply False.elim assump_48
      case inr assump_29 =>
        cases assump_3
        case intro assump_54 assump_55 =>
          cases assump_54
          case inl assump_56 =>
            have assump_78 : True := by
              apply True.intro
            let assump_62 := assump_55 assump_78
            apply False.elim assump_62
          case inr assump_57 =>
            have assump_79 : True := by
              apply True.intro
            let assump_70 := assump_55 assump_79
            apply False.elim assump_70


variable (p4 p1 p5 p2 p3 p0 p6 : Prop)
theorem file81_49519 : (((((True ∧ p1) → False) → ((p1 ∨ p2) → (p2 ∨ p0))) ∨ (((p3 ∧ p3) ∧ (p6 ∨ p1)) ∨ ((True → False) → False))) ∨ ((((p4 ∧ p5) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_17 : (True ∧ p1) := by
      apply And.intro
      apply True.intro
      exact assump_3
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  case inr assump_4 =>
    apply Or.inl
    exact assump_4


variable (p0 p3 p6 p4 p2 : Prop)
theorem file81_50070 : (((((p3 → False) ∧ (p4 ∧ False)) → False) ∧ (((p6 ∧ p4) → False) ∧ ((p2 ∨ p0) ∧ (False ∧ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        case inr assump_13 =>
          cases assump_11
          case intro assump_22 assump_23 =>
            apply False.elim assump_22


variable (p1 p5 p0 p6 p2 p7 : Prop)
theorem file81_50727 : (((((p7 ∨ True) ∨ (p2 ∧ p2)) → ((False → False) ∧ (p7 → False))) → (((p7 ∨ p2) ∧ (p2 ∨ p1)) → ((p2 → p2) → (p7 → False)))) ∨ ((((p7 → p6) ∧ (p7 ∨ p0)) → False) → (((False → p6) → (False ∧ p2)) → ((p5 ∨ False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_10
      case inl assump_15 =>
        have assump_65 : ((p7 ∨ True) ∨ (p2 ∧ p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_21 := assump_1 assump_65
        let assump_22 := And.right assump_21
        have assump_66 : p7 := by
          exact assump_11
        let assump_24 := assump_22 assump_66
        apply False.elim assump_24
      case inr assump_16 =>
        have assump_67 : ((p7 ∨ True) ∨ (p2 ∧ p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_32 := assump_1 assump_67
        let assump_33 := And.right assump_32
        have assump_68 : p7 := by
          exact assump_11
        let assump_35 := assump_33 assump_68
        apply False.elim assump_35
    case inr assump_12 =>
      cases assump_10
      case inl assump_41 =>
        have assump_69 : ((p7 ∨ True) ∨ (p2 ∧ p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_4
        let assump_47 := assump_1 assump_69
        let assump_48 := And.right assump_47
        have assump_70 : p7 := by
          exact assump_4
        let assump_50 := assump_48 assump_70
        apply False.elim assump_50
      case inr assump_42 =>
        have assump_71 : ((p7 ∨ True) ∨ (p2 ∧ p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_4
        let assump_58 := assump_1 assump_71
        let assump_59 := And.right assump_58
        have assump_72 : p7 := by
          exact assump_4
        let assump_61 := assump_59 assump_72
        apply False.elim assump_61


variable (p2 p5 p4 p3 p6 p7 p1 : Prop)
theorem file81_52807 : (((((False → False) → False) ∧ ((p4 ∨ p2) ∧ (p4 ∨ False))) → (((p3 → p6) ∧ (p4 → True)) → ((True → False) ∨ (True ∧ p1)))) ∨ ((((p6 ∨ p7) ∧ (p3 ∨ False)) ∧ ((p2 ∧ p6) → False)) → (((p2 ∧ p5) ∧ (False ∨ p3)) ∧ ((p1 ∧ False) ∧ (p3 → p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_14
          case inl assump_19 =>
            apply Or.inl
            intro assump_23
            have assump_57 : (False → False) := by
              intro assump_29
              apply False.elim assump_29
            let assump_28 := assump_9 assump_57
            apply False.elim assump_28
          case inr assump_20 =>
            apply False.elim assump_20
        case inr assump_16 =>
          cases assump_14
          case inl assump_39 =>
            apply Or.inl
            intro assump_43
            have assump_58 : (False → False) := by
              intro assump_49
              apply False.elim assump_49
            let assump_48 := assump_9 assump_58
            apply False.elim assump_48
          case inr assump_40 =>
            apply False.elim assump_40


variable (p2 p7 p6 p3 p0 : Prop)
theorem file81_54193 : ((((((True → False) → (p6 → False)) ∨ ((p2 → False) → (p3 ∨ p2))) ∨ (((p7 ∧ p0) ∨ (p7 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True → False) → (p6 → False)) ∨ ((p2 → False) → (p3 ∨ p2))) ∨ (((p7 ∧ p0) ∨ (p7 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p5 p0 p7 p2 : Prop)
theorem file81_54789 : ((((((p2 → p3) ∧ (p2 → False)) ∨ ((p2 ∨ p5) → False)) → (((p7 → p7) ∨ (False ∧ True)) ∧ ((True → p0) ∧ (p7 ∧ p2)))) ∧ ((((p5 ∧ p2) → (p0 ∨ p5)) ∨ ((True ∧ True) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p5 ∧ p2) → (p0 ∨ p5)) ∨ ((True ∧ True) → False)) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        exact assump_10
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p5 p3 p6 p4 p0 p2 p1 : Prop)
theorem file81_55410 : (((((p5 → p0) → (p4 ∨ p6)) ∨ ((p6 ∧ p5) ∧ (True → False))) → False) → ((((p2 ∨ p3) ∨ (p4 → p1)) → False) → (((p4 ∧ p3) → (p5 → p5)) ∨ ((False → True) → False)))) := by
  intro assump_10
  intro assump_11
  apply Or.inl
  intro assump_16
  intro assump_17
  cases assump_16
  case intro assump_20 assump_21 =>
    exact assump_17


variable (p2 p5 p0 p1 p4 p6 : Prop)
theorem file81_55799 : (((((True → False) → False) ∨ ((p4 → p2) → False)) ∨ (((p4 ∧ p4) ∨ (True ∨ True)) → False)) ∨ ((((p1 → False) ∧ (p0 ∧ p5)) → ((p6 ∨ p2) → (p1 → False))) ∨ (((p2 → p0) → (p5 ∧ p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_10
  have assump_17 : True := by
    apply True.intro
  let assump_13 := assump_10 assump_17
  apply False.elim assump_13


variable (p3 p6 p2 p4 p1 p5 p0 p7 : Prop)
theorem file81_56244 : (((((True → False) ∨ (p2 ∧ False)) ∧ ((p7 ∨ p7) ∨ (p1 → p3))) → (((p3 ∨ p5) → (p7 ∨ p1)) → ((p4 → False) ∨ (p4 ∨ p6)))) ∨ ((((p3 ∨ p4) → False) → ((p6 → p4) → (p3 → False))) ∨ (((p7 ∨ p0) → (p3 → p7)) ∨ ((p0 → False) ∧ (p1 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          intro assump_17
          have assump_54 : True := by
            apply True.intro
          let assump_22 := assump_7 assump_54
          apply False.elim assump_22
        case inr assump_14 =>
          apply Or.inl
          intro assump_28
          have assump_55 : True := by
            apply True.intro
          let assump_33 := assump_7 assump_55
          apply False.elim assump_33
      case inr assump_12 =>
        apply Or.inl
        intro assump_39
        have assump_56 : True := by
          apply True.intro
        let assump_44 := assump_7 assump_56
        apply False.elim assump_44
    case inr assump_8 =>
      cases assump_8
      case intro assump_48 assump_49 =>
        apply False.elim assump_49


variable (p2 p7 p5 : Prop)
theorem file81_57545 : ((((((p7 ∨ True) → False) → False) ∨ (((p2 ∧ p5) → False) ∧ ((p5 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 ∨ True) → False) → False) ∨ (((p2 ∧ p5) → False) ∧ ((p5 → False) → False))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p7 p1 p6 p2 p5 : Prop)
theorem file81_58090 : (((((p6 ∨ p5) ∧ (p4 → False)) → ((p5 → p7) → (p6 ∧ True))) ∧ (((p7 → p4) → False) ∧ ((False ∧ True) ∧ (p1 → p2)))) → ((((True → p1) → (p5 ∨ p5)) ∨ ((p7 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
  case inr assump_4 =>
    cases assump_1
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        cases assump_28
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            apply False.elim assump_33


variable (p3 p7 p4 p0 p6 p5 p1 : Prop)
theorem file81_59022 : (((((p5 ∧ p6) ∨ (True → p7)) ∨ ((True → p5) → False)) ∧ (((p0 → False) ∧ (False ∧ p3)) ∧ ((p7 → p6) ∧ (True → False)))) → ((((p0 ∨ p7) → (True ∨ p5)) → False) ∨ (((p6 ∨ p5) ∨ (p6 ∨ p4)) → ((p1 ∧ p7) → (p0 → False))))) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case inl assump_21 =>
      cases assump_21
      case inl assump_23 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_20
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              cases assump_34
              case intro assump_37 assump_38 =>
                apply False.elim assump_37
      case inr assump_24 =>
        cases assump_20
        case intro assump_43 assump_44 =>
          cases assump_43
          case intro assump_45 assump_46 =>
            cases assump_46
            case intro assump_49 assump_50 =>
              apply False.elim assump_49
    case inr assump_22 =>
      cases assump_20
      case intro assump_55 assump_56 =>
        cases assump_55
        case intro assump_57 assump_58 =>
          cases assump_58
          case intro assump_61 assump_62 =>
            apply False.elim assump_61


variable (p5 p1 p3 p4 p2 p7 : Prop)
theorem file81_60347 : (((((p3 ∧ p5) ∨ (p4 ∨ True)) ∨ ((p4 → p2) → False)) ∨ (((p3 → p7) → False) → False)) ∨ ((((p2 → False) ∨ (p4 → False)) ∨ ((p5 ∧ p1) → (p7 ∧ p1))) ∧ (((p4 ∨ p3) ∨ (p4 ∨ p1)) → ((True → p5) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p2 p4 p0 p1 p5 p3 p7 : Prop)
theorem file81_60710 : (((((p7 ∨ True) ∧ (p3 → True)) ∨ ((p4 ∨ p5) ∧ (p7 → p2))) → False) → ((((p7 → p1) → False) ∧ ((p3 ∨ True) ∧ (p1 ∧ p7))) ∧ (((p5 → p2) → False) ∨ ((p4 → p0) → (p3 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_39 : (((p7 ∨ True) ∧ (p3 → True)) ∨ ((p4 ∨ p5) ∧ (p7 → p2))) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply True.intro
    intro assump_8
    apply True.intro
  let assump_7 := assump_1 assump_39
  apply False.elim assump_7
  apply And.intro
  apply Or.inr
  apply True.intro
  apply And.intro
  have assump_40 : (((p7 ∨ True) ∧ (p3 → True)) ∨ ((p4 ∨ p5) ∧ (p7 → p2))) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply True.intro
    intro assump_17
    apply True.intro
  let assump_16 := assump_1 assump_40
  apply False.elim assump_16
  have assump_41 : (((p7 ∨ True) ∧ (p3 → True)) ∨ ((p4 ∨ p5) ∧ (p7 → p2))) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply True.intro
    intro assump_24
    apply True.intro
  let assump_23 := assump_1 assump_41
  apply False.elim assump_23
  apply Or.inl
  intro assump_30
  have assump_42 : (((p7 ∨ True) ∧ (p3 → True)) ∨ ((p4 ∨ p5) ∧ (p7 → p2))) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply True.intro
    intro assump_35
    apply True.intro
  let assump_34 := assump_1 assump_42
  apply False.elim assump_34


variable (p2 p6 p1 p3 p5 p0 p4 : Prop)
theorem file81_62180 : (((((False → False) → False) → ((True ∧ p4) ∨ (p5 → p3))) → False) → ((((p0 → p2) → (p6 → False)) ∧ ((p1 ∧ p0) ∧ (True ∨ p5))) ∨ (((p3 → False) ∧ (p4 ∧ p5)) → False))) := by
  intro assump_10
  apply Or.inr
  intro assump_39
  cases assump_39
  case intro assump_40 assump_41 =>
    cases assump_41
    case intro assump_44 assump_45 =>
      have assump_60 : (((False → False) → False) → ((True ∧ p4) ∨ (p5 → p3))) := by
        intro assump_54
        apply Or.inl
        apply And.intro
        apply True.intro
        exact assump_44
      let assump_53 := assump_10 assump_60
      apply False.elim assump_53


variable (p4 p2 p1 p5 p6 : Prop)
theorem file81_62853 : (((((p5 ∧ False) → False) → False) → (((p4 ∧ p4) → (p6 ∨ p2)) → ((p6 → False) → False))) ∨ ((((False → False) → False) ∨ ((p1 ∧ p4) ∧ (p4 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_21 : ((p5 ∧ False) → False) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  let assump_10 := assump_1 assump_21
  apply False.elim assump_10


variable (p3 p1 p5 p6 : Prop)
theorem file81_63361 : (((((p3 ∨ p1) → (False → p5)) ∨ ((p5 ∨ True) ∧ (p6 → False))) → False) → False) := by
  intro assump_8
  have assump_19 : (((p3 ∨ p1) → (False → p5)) ∨ ((p5 ∨ True) ∧ (p6 → False))) := by
    apply Or.inl
    intro assump_12
    intro assump_13
    apply False.elim assump_13
  let assump_11 := assump_8 assump_19
  apply False.elim assump_11


variable (p1 p2 p7 p4 p5 p3 : Prop)
theorem file81_63764 : ((((((p3 ∧ True) → False) → ((p1 ∨ p2) → (True ∨ p2))) → False) ∧ ((((p5 ∨ True) ∧ (p2 ∧ p5)) ∨ ((p7 ∨ p4) ∧ (p3 ∧ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p3 ∧ True) → False) → ((p1 ∨ p2) → (True ∨ p2))) := by
      intro assump_10
      intro assump_11
      cases assump_11
      case inl assump_12 =>
        apply Or.inl
        apply True.intro
      case inr assump_13 =>
        apply Or.inl
        apply True.intro
    let assump_9 := assump_2 assump_25
    apply False.elim assump_9


variable (p7 p0 p2 p3 p6 p5 p4 p1 : Prop)
theorem file81_64409 : ((((((p4 → True) ∨ (p6 ∨ p5)) → False) → (((p4 ∧ p1) ∧ (p3 → False)) ∧ ((p2 ∨ p0) → (p7 → p0)))) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p4 → True) ∨ (p6 ∨ p5)) → False) → (((p4 ∧ p1) ∧ (p3 → False)) ∧ ((p2 ∨ p0) → (p7 → p0)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    have assump_53 : ((p4 → True) ∨ (p6 ∨ p5)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_53
    apply False.elim assump_8
    have assump_54 : ((p4 → True) ∨ (p6 ∨ p5)) := by
      apply Or.inl
      intro assump_16
      apply True.intro
    let assump_15 := assump_5 assump_54
    apply False.elim assump_15
    intro assump_20
    have assump_55 : ((p4 → True) ∨ (p6 ∨ p5)) := by
      apply Or.inl
      intro assump_26
      apply True.intro
    let assump_25 := assump_5 assump_55
    apply False.elim assump_25
    intro assump_30
    intro assump_31
    cases assump_30
    case inl assump_34 =>
      have assump_56 : ((p4 → True) ∨ (p6 ∨ p5)) := by
        apply Or.inl
        intro assump_41
        apply True.intro
      let assump_40 := assump_5 assump_56
      apply False.elim assump_40
    case inr assump_35 =>
      exact assump_35
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p2 p4 p5 p7 p0 : Prop)
theorem file81_65783 : (((((p0 ∧ p7) ∧ (p5 ∧ True)) ∨ ((False → False) ∨ (p2 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p0 ∧ p7) ∧ (p5 ∧ True)) ∨ ((False → False) ∨ (p2 ∨ p4))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p1 p5 : Prop)
theorem file81_66170 : (((((False ∧ p4) ∧ (p5 ∧ p1)) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∧ p4) ∧ (p5 ∧ p1)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p1 p7 p6 p0 p3 p4 p5 : Prop)
theorem file81_66610 : (((((False ∧ p0) ∧ (p5 ∨ p2)) → ((p7 ∧ False) → False)) → False) → ((((p2 ∨ p4) ∨ (p0 ∧ p4)) ∨ ((p2 → False) → (p1 ∨ p2))) ∧ (((p5 ∧ p4) → False) ∨ ((p3 ∨ p0) → (p6 ∨ p3))))) := by
  intro assump_5
  apply And.intro
  apply Or.inr
  intro assump_8
  have assump_47 : (((False ∧ p0) ∧ (p5 ∨ p2)) → ((p7 ∧ False) → False)) := by
    intro assump_13
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_16
  let assump_12 := assump_5 assump_47
  apply False.elim assump_12
  apply Or.inl
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    have assump_48 : (((False ∧ p0) ∧ (p5 ∨ p2)) → ((p7 ∧ False) → False)) := by
      intro assump_36
      intro assump_37
      cases assump_37
      case intro assump_38 assump_39 =>
        apply False.elim assump_39
    let assump_35 := assump_5 assump_48
    apply False.elim assump_35


variable (p5 p0 p4 p2 p3 p7 : Prop)
theorem file81_67575 : ((((((True → False) ∧ (False ∧ p4)) → ((p0 ∨ p3) → False)) ∨ (((p5 → False) ∨ (p2 → p0)) ∨ ((p3 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((True → False) ∧ (False ∧ p4)) → ((p0 ∨ p3) → False)) ∨ (((p5 → False) ∨ (p2 → p0)) ∨ ((p3 ∨ p7) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
    case inr assump_8 =>
      cases assump_5
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 : Prop)
theorem file81_68427 : (((((p1 → p1) → (True → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : (((p1 → p1) → (True → False)) → False) := by
    intro assump_5
    have assump_20 : (p1 → p1) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_20
    have assump_21 : True := by
      apply True.intro
    let assump_12 := assump_8 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p7 p0 p6 p5 p3 : Prop)
theorem file81_68961 : ((((((p0 ∨ p1) ∨ (p3 ∨ p3)) ∧ ((p0 → p6) ∨ (p5 ∧ p6))) ∨ (((p7 ∨ True) → (False ∨ False)) → ((p0 ∧ p6) ∧ (p3 → False)))) ∧ ((((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_11
            case inl assump_18 =>
              have assump_194 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                apply Or.inr
                intro assump_25
                intro assump_26
                exact assump_14
              let assump_24 := assump_7 assump_194
              apply False.elim assump_24
            case inr assump_19 =>
              cases assump_19
              case intro assump_34 assump_35 =>
                have assump_195 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                  apply Or.inr
                  intro assump_43
                  intro assump_44
                  exact assump_14
                let assump_42 := assump_7 assump_195
                apply False.elim assump_42
          case inr assump_15 =>
            cases assump_11
            case inl assump_54 =>
              have assump_196 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                apply Or.inr
                intro assump_61
                intro assump_62
                have assump_197 : True := by
                  apply True.intro
                let assump_67 := assump_61 assump_197
                apply False.elim assump_67
              let assump_60 := assump_7 assump_196
              apply False.elim assump_60
            case inr assump_55 =>
              cases assump_55
              case intro assump_74 assump_75 =>
                have assump_198 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                  apply Or.inl
                  apply And.intro
                  apply And.intro
                  exact assump_15
                  exact assump_74
                  apply Or.inl
                  exact assump_75
                let assump_82 := assump_7 assump_198
                apply False.elim assump_82
        case inr assump_13 =>
          cases assump_13
          case inl assump_86 =>
            cases assump_11
            case inl assump_90 =>
              have assump_199 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                apply Or.inr
                intro assump_97
                intro assump_98
                have assump_200 : True := by
                  apply True.intro
                let assump_103 := assump_97 assump_200
                apply False.elim assump_103
              let assump_96 := assump_7 assump_199
              apply False.elim assump_96
            case inr assump_91 =>
              cases assump_91
              case intro assump_110 assump_111 =>
                have assump_201 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                  apply Or.inr
                  intro assump_119
                  intro assump_120
                  have assump_202 : True := by
                    apply True.intro
                  let assump_125 := assump_119 assump_202
                  apply False.elim assump_125
                let assump_118 := assump_7 assump_201
                apply False.elim assump_118
          case inr assump_87 =>
            cases assump_11
            case inl assump_134 =>
              have assump_203 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                apply Or.inr
                intro assump_141
                intro assump_142
                have assump_204 : True := by
                  apply True.intro
                let assump_147 := assump_141 assump_204
                apply False.elim assump_147
              let assump_140 := assump_7 assump_203
              apply False.elim assump_140
            case inr assump_135 =>
              cases assump_135
              case intro assump_154 assump_155 =>
                have assump_205 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
                  apply Or.inr
                  intro assump_163
                  intro assump_164
                  have assump_206 : True := by
                    apply True.intro
                  let assump_169 := assump_163 assump_206
                  apply False.elim assump_169
                let assump_162 := assump_7 assump_205
                apply False.elim assump_162
    case inr assump_9 =>
      have assump_207 : (((p1 ∧ p5) ∧ (p6 ∨ True)) ∨ ((True → False) → (True → p0))) := by
        apply Or.inr
        intro assump_181
        intro assump_182
        have assump_208 : True := by
          apply True.intro
        let assump_187 := assump_181 assump_208
        apply False.elim assump_187
      let assump_180 := assump_7 assump_207
      apply False.elim assump_180


variable (p6 p5 p1 p4 p2 : Prop)
theorem file81_74224 : (((((True ∧ p2) ∨ (p5 ∧ True)) → False) → (((True ∧ False) ∧ (p2 → False)) ∨ ((p1 ∧ p4) → (p2 → False)))) ∨ ((((False → False) ∨ (p2 ∨ p6)) ∧ ((p5 ∨ p4) → (p2 → False))) → False)) := by
  apply Or.inl
  intro assump_4
  apply Or.inr
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    have assump_24 : ((True ∧ p2) ∨ (p5 ∧ True)) := by
      apply Or.inl
      apply And.intro
      apply True.intro
      exact assump_8
    let assump_20 := assump_4 assump_24
    apply False.elim assump_20


variable (p7 p5 p4 p2 p1 : Prop)
theorem file81_74812 : ((((((False → p2) → (p2 ∧ p4)) ∨ ((p7 → p1) ∨ (False ∨ p2))) → (((True ∨ p7) ∨ (p5 → False)) ∨ ((p5 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → p2) → (p2 ∧ p4)) ∨ ((p7 → p1) ∨ (False ∨ p2))) → (((True ∨ p7) ∨ (p5 → False)) ∨ ((p5 ∨ p7) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p0 p6 p5 p7 p2 p3 p1 : Prop)
theorem file81_75788 : (((((p7 → False) ∨ (True ∧ p7)) → ((False → p3) ∨ (p0 ∧ p7))) ∨ (((p1 → False) ∧ (p2 ∧ p5)) → False)) ∨ ((((p5 → False) ∨ (p7 ∨ p0)) → ((p5 ∨ p6) → False)) ∧ (((p5 ∨ p5) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      apply Or.inl
      intro assump_15
      apply False.elim assump_15


variable (p1 p5 p7 p3 : Prop)
theorem file81_76344 : (((((False ∧ p7) ∧ (False ∨ p3)) ∧ ((p7 → False) → False)) ∧ (((p1 → p7) ∧ (p1 → False)) ∨ ((True → p1) → False))) → ((((False → False) ∨ (p3 → False)) → ((p7 ∧ p1) → (p3 → False))) ∨ (((p5 → False) → (False → False)) → False))) := by
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


variable (p6 p1 p0 p5 p4 : Prop)
theorem file81_76917 : (((((False ∧ p4) ∧ (p6 ∧ p5)) ∧ ((p0 → False) ∧ (True → False))) ∧ (((p6 → True) ∧ (p6 ∨ p5)) → ((p6 ∧ p1) ∧ (p1 → p6)))) → False) := by
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


variable (p6 p2 p3 p7 p4 : Prop)
theorem file81_77392 : ((((((p3 ∨ p6) ∨ (False → False)) → False) → (((p2 ∧ p4) ∧ (p7 ∨ p7)) ∨ ((p4 → False) ∨ (p7 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p3 ∨ p6) ∨ (False → False)) → False) → (((p2 ∧ p4) ∧ (p7 ∨ p7)) ∨ ((p4 → False) ∨ (p7 ∧ p2)))) := by
    intro assump_5
    apply Or.inr
    apply Or.inl
    intro assump_8
    have assump_23 : ((p3 ∨ p6) ∨ (False → False)) := by
      apply Or.inr
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p2 p5 p0 p7 p6 : Prop)
theorem file81_78057 : ((((((False ∧ True) → (p6 → True)) ∨ ((p4 → False) ∨ (p4 → p0))) ∨ (((p5 ∨ p6) → (False → p2)) ∨ ((p2 → False) ∨ (p7 → False)))) → False) → False) := by
  intro assump_11
  have assump_20 : ((((False ∧ True) → (p6 → True)) ∨ ((p4 → False) ∨ (p4 → p0))) ∨ (((p5 ∨ p6) → (False → p2)) ∨ ((p2 → False) ∨ (p7 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_15
    intro assump_16
    apply True.intro
  let assump_14 := assump_11 assump_20
  apply False.elim assump_14


variable (p1 p4 p5 : Prop)
theorem file81_78594 : ((((((p1 ∧ True) → (True → False)) ∧ ((True ∨ p4) → (False ∧ False))) → (((True ∨ p5) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 ∧ True) → (True → False)) ∧ ((True ∨ p4) → (False ∧ False))) → (((True ∨ p5) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_24 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_15 := assump_10 assump_24
      let assump_16 := And.left assump_15
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p7 p2 p5 : Prop)
theorem file81_79286 : ((((((p7 → p4) → (p2 → p7)) ∨ ((p4 ∨ p7) → (p4 → False))) → (((True → False) → (p7 → False)) ∨ ((p4 ∨ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p7 → p4) → (p2 → p7)) ∨ ((p4 ∨ p7) → (p4 → False))) → (((True → False) → (p7 → False)) ∨ ((p4 ∨ p5) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      have assump_36 : True := by
        apply True.intro
      let assump_16 := assump_10 assump_36
      apply False.elim assump_16
    case inr assump_7 =>
      apply Or.inl
      intro assump_22
      intro assump_23
      have assump_37 : True := by
        apply True.intro
      let assump_28 := assump_22 assump_37
      apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p0 p4 p3 p2 p1 : Prop)
theorem file81_80190 : (((((p2 → p2) ∨ (p4 → p0)) → False) ∧ (((p3 ∨ p4) → False) ∨ ((False → False) → (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_32 : ((p2 → p2) ∨ (p4 → p0)) := by
        apply Or.inl
        intro assump_12
        exact assump_12
      let assump_11 := assump_2 assump_32
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_33 : ((p2 → p2) ∨ (p4 → p0)) := by
        apply Or.inl
        intro assump_26
        exact assump_26
      let assump_25 := assump_2 assump_33
      apply False.elim assump_25


variable (p6 p5 p3 p4 p2 p7 p0 : Prop)
theorem file81_80895 : (((((p7 ∨ True) ∧ (p3 → p4)) → False) → (((True ∨ p6) ∨ (True → p2)) ∧ ((False ∧ p5) → False))) ∨ ((((p3 → p5) → (False ∧ False)) ∨ ((False → p4) → False)) → (((True → p2) → False) → ((True ∨ p3) ∧ (p3 → p0))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply True.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p1 p4 p5 p3 p2 p7 p0 : Prop)
theorem file81_81373 : (((((p3 ∨ p3) → False) → ((False ∨ False) ∧ (p4 ∨ p5))) ∧ (((p4 → False) → False) ∧ ((p2 ∧ True) ∨ (p5 ∧ p7)))) → ((((p5 ∧ p0) ∧ (p0 ∧ p7)) ∨ ((p5 → False) → (False → False))) ∨ (((p3 → p1) ∨ (p0 ∧ p2)) ∨ ((p3 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inr
          intro assump_18
          intro assump_19
          apply False.elim assump_19
      case inr assump_11 =>
        cases assump_11
        case intro assump_22 assump_23 =>
          apply Or.inl
          apply Or.inr
          intro assump_28
          intro assump_29
          apply False.elim assump_29


variable (p6 p4 p2 p7 : Prop)
theorem file81_82266 : (((((p4 ∧ p7) ∨ (p2 → False)) ∧ ((True → p6) → (True → False))) ∧ (((p4 ∧ p4) ∨ (True → p2)) ∧ ((p2 → False) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_17
                case intro assump_26 assump_27 =>
                  have assump_84 : True := by
                    apply True.intro
                  let assump_32 := assump_27 assump_84
                  apply False.elim assump_32
            case inr assump_19 =>
              cases assump_17
              case intro assump_38 assump_39 =>
                have assump_85 : True := by
                  apply True.intro
                let assump_44 := assump_39 assump_85
                apply False.elim assump_44
      case inr assump_7 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          cases assump_52
          case inl assump_54 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              cases assump_53
              case intro assump_62 assump_63 =>
                have assump_86 : True := by
                  apply True.intro
                let assump_68 := assump_63 assump_86
                apply False.elim assump_68
          case inr assump_55 =>
            cases assump_53
            case intro assump_74 assump_75 =>
              have assump_87 : True := by
                apply True.intro
              let assump_80 := assump_75 assump_87
              apply False.elim assump_80


variable (p7 p6 p5 p4 p1 p2 p3 p0 : Prop)
theorem file81_84221 : (((((p0 → False) ∨ (p6 ∨ p4)) → ((False → p0) ∨ (p6 → False))) ∨ (((p1 ∨ p7) ∨ (p3 ∨ p7)) → ((False ∧ True) → (p7 ∧ p2)))) ∨ ((((p0 ∨ p7) → (p0 ∧ p5)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_9 =>
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    case inr assump_10 =>
      apply Or.inl
      intro assump_18
      apply False.elim assump_18


variable (p5 p2 p4 p7 p0 p6 p1 : Prop)
theorem file81_84854 : (((((True ∨ p7) → False) ∨ ((p6 → False) ∧ (p0 ∨ False))) → (((p5 ∧ p0) ∨ (p6 ∧ True)) → ((p5 → False) → False))) ∨ ((((False ∨ p4) → False) → False) → (((p5 → False) → (p2 ∨ p0)) → ((p1 → False) ∨ (p6 → True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_1
      case inl assump_14 =>
        have assump_69 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_18 := assump_14 assump_69
        apply False.elim assump_18
      case inr assump_15 =>
        cases assump_15
        case intro assump_22 assump_23 =>
          cases assump_23
          case inl assump_26 =>
            have assump_70 : p5 := by
              exact assump_8
            let assump_34 := assump_3 assump_70
            apply False.elim assump_34
          case inr assump_27 =>
            apply False.elim assump_27
  case inr assump_7 =>
    cases assump_7
    case intro assump_40 assump_41 =>
      cases assump_1
      case inl assump_46 =>
        have assump_71 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_50 := assump_46 assump_71
        apply False.elim assump_50
      case inr assump_47 =>
        cases assump_47
        case intro assump_54 assump_55 =>
          cases assump_55
          case inl assump_58 =>
            have assump_72 : p6 := by
              exact assump_40
            let assump_63 := assump_54 assump_72
            apply False.elim assump_63
          case inr assump_59 =>
            apply False.elim assump_59


variable (p2 p5 p1 p3 p0 : Prop)
theorem file81_86572 : ((((((p2 ∧ p3) ∧ (True → False)) ∧ ((p5 ∧ p0) → (True → False))) → (((False → p1) → False) ∧ ((p1 → p5) → False))) → False) → False) := by
  intro assump_1
  have assump_53 : ((((p2 ∧ p3) ∧ (True → False)) ∧ ((p5 ∧ p0) → (True → False))) → (((False → p1) → False) ∧ ((p1 → p5) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_54 : True := by
            apply True.intro
          let assump_24 := assump_12 assump_54
          apply False.elim assump_24
    intro assump_28
    cases assump_5
    case intro assump_31 assump_32 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          have assump_55 : True := by
            apply True.intro
          let assump_46 := assump_34 assump_55
          apply False.elim assump_46
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p0 p4 p2 p3 p5 : Prop)
theorem file81_87736 : ((((((p2 → False) ∧ (False ∧ p4)) ∧ ((p5 ∧ p3) → (p0 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p2 → False) ∧ (False ∧ p4)) ∧ ((p5 ∧ p3) → (p0 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p2 p7 p0 : Prop)
theorem file81_88300 : ((((((False ∨ p5) ∧ (p2 ∧ p0)) ∧ ((False → p5) → False)) → (((p7 → False) → False) → ((p0 ∨ True) → False))) → False) → False) := by
  intro assump_1
  have assump_71 : ((((False ∨ p5) ∧ (p2 ∧ p0)) ∧ ((False → p5) → False)) → (((p7 → False) → False) → ((p0 ∨ True) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            apply False.elim assump_18
          case inr assump_19 =>
            cases assump_17
            case intro assump_24 assump_25 =>
              have assump_72 : (False → p5) := by
                intro assump_33
                apply False.elim assump_33
              let assump_32 := assump_15 assump_72
              apply False.elim assump_32
    case inr assump_9 =>
      cases assump_5
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          cases assump_45
          case inl assump_47 =>
            apply False.elim assump_47
          case inr assump_48 =>
            cases assump_46
            case intro assump_53 assump_54 =>
              have assump_73 : (False → p5) := by
                intro assump_62
                apply False.elim assump_62
              let assump_61 := assump_44 assump_73
              apply False.elim assump_61
  let assump_4 := assump_1 assump_71
  apply False.elim assump_4


variable (p4 p5 p1 p7 p3 p2 : Prop)
theorem file81_89927 : (((((p1 ∧ p2) ∧ (p5 → False)) → ((p2 → p5) → (p7 → p4))) → (((False → False) → False) → ((p5 → p1) → False))) ∨ ((((p1 ∧ p7) ∨ (p3 → True)) ∨ ((False → p4) ∨ (p7 → False))) → False)) := by
  apply Or.inl
  intro assump_13
  intro assump_14
  intro assump_15
  have assump_30 : (False → False) := by
    intro assump_24
    apply False.elim assump_24
  let assump_23 := assump_14 assump_30
  apply False.elim assump_23


variable (p6 p3 p5 p0 p7 p1 p4 : Prop)
theorem file81_90408 : ((((((p7 ∨ p3) → (p6 ∧ p0)) ∧ ((p6 → p7) ∧ (p6 ∧ p7))) → False) ∧ ((((p1 ∨ p4) → False) ∧ ((p0 ∨ p3) ∧ (False ∧ p7))) ∧ (((p1 ∧ p5) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
          case inr assump_15 =>
            cases assump_13
            case intro assump_24 assump_25 =>
              apply False.elim assump_24


variable (p3 p5 p0 p2 p7 p1 p6 p4 : Prop)
theorem file81_91208 : (((((p6 → False) → (p3 → p1)) → False) ∨ (((True → p3) ∨ (p2 → False)) ∨ ((p7 ∧ p6) → False))) → ((((p0 ∧ p5) ∧ (p2 ∧ p6)) → ((p4 → p6) ∨ (p3 ∨ p4))) ∨ (((p6 → False) → False) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply Or.inl
          intro assump_21
          exact assump_16
  case inr assump_3 =>
    cases assump_3
    case inl assump_24 =>
      cases assump_24
      case inl assump_26 =>
        apply Or.inl
        intro assump_30
        cases assump_30
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            cases assump_32
            case intro assump_39 assump_40 =>
              apply Or.inl
              intro assump_45
              exact assump_40
      case inr assump_27 =>
        apply Or.inl
        intro assump_50
        cases assump_50
        case intro assump_51 assump_52 =>
          cases assump_51
          case intro assump_53 assump_54 =>
            cases assump_52
            case intro assump_59 assump_60 =>
              apply Or.inl
              intro assump_65
              exact assump_60
    case inr assump_25 =>
      apply Or.inl
      intro assump_70
      cases assump_70
      case intro assump_71 assump_72 =>
        cases assump_71
        case intro assump_73 assump_74 =>
          cases assump_72
          case intro assump_79 assump_80 =>
            apply Or.inl
            intro assump_85
            exact assump_80


variable (p3 p5 p6 p7 p1 : Prop)
theorem file81_92982 : (((((p6 ∨ p5) → (p5 ∨ True)) → False) ∧ (((p7 ∨ p7) ∧ (p3 ∧ p3)) → ((p1 ∧ p7) ∧ (p1 ∨ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((p6 ∨ p5) → (p5 ∨ True)) := by
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        apply Or.inr
        apply True.intro
      case inr assump_12 =>
        apply Or.inl
        exact assump_12
    let assump_9 := assump_2 assump_20
    apply False.elim assump_9


variable (p7 p3 p0 p4 p6 p1 p5 : Prop)
theorem file81_93534 : ((((((p3 → False) → (p7 → p7)) ∨ ((p4 ∨ True) → (p0 → False))) ∨ (((p1 → p4) ∧ (p5 → True)) ∨ ((p1 ∧ p5) ∨ (p6 → False)))) → False) → False) := by
  intro assump_17
  have assump_30 : ((((p3 → False) → (p7 → p7)) ∨ ((p4 ∨ True) → (p0 → False))) ∨ (((p1 → p4) ∧ (p5 → True)) ∨ ((p1 ∧ p5) ∨ (p6 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_21
    intro assump_22
    exact assump_22
  let assump_20 := assump_17 assump_30
  apply False.elim assump_20


variable (p4 p5 p0 p6 p2 p1 p3 p7 : Prop)
theorem file81_94073 : (((((False → p3) → (p5 → p6)) ∧ ((p2 ∨ p0) → (p1 → p1))) → (((p1 ∧ p3) → (True → True)) → ((p6 ∧ False) ∨ (True ∧ p5)))) → ((((p4 → p2) → (p2 → p6)) ∨ ((p7 → False) ∨ (True ∨ p5))) → (((p4 ∧ p2) ∧ (True → p1)) → ((p0 ∨ p0) ∨ (p2 ∨ False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case inl assump_14 =>
        apply Or.inr
        apply Or.inl
        exact assump_7
      case inr assump_15 =>
        cases assump_15
        case inl assump_20 =>
          apply Or.inr
          apply Or.inl
          exact assump_7
        case inr assump_21 =>
          cases assump_21
          case inl assump_26 =>
            apply Or.inr
            apply Or.inl
            exact assump_7
          case inr assump_27 =>
            apply Or.inr
            apply Or.inl
            exact assump_7


variable (p6 p7 p0 p3 : Prop)
theorem file81_95073 : (((((False ∧ True) ∧ (False ∧ p6)) → ((p3 ∨ p0) → (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_31 : (((False ∧ True) ∧ (False ∧ p6)) → ((p3 ∨ p0) → (p7 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
    case inr assump_11 =>
      cases assump_5
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p7 p3 p0 p4 p2 p5 : Prop)
theorem file81_95851 : (((((p4 ∧ p1) → (True ∧ p4)) → ((p7 → False) ∨ (p5 → p4))) → (((False ∨ False) → False) ∨ ((p2 ∨ p5) → (False → p7)))) ∨ ((((True ∨ p1) → (p1 ∧ p0)) ∨ ((p3 ∧ p7) → (True → False))) → False)) := by
  apply Or.inl
  intro assump_10
  apply Or.inl
  intro assump_13
  cases assump_13
  case inl assump_14 =>
    apply False.elim assump_14
  case inr assump_15 =>
    apply False.elim assump_15


variable (p4 p1 p5 p3 p0 p6 p7 : Prop)
theorem file81_96305 : (((((p1 ∧ False) → (p4 → p0)) ∨ ((p1 → False) ∧ (p3 → False))) ∨ (((p5 ∧ p7) ∧ (p7 → p0)) ∨ ((p1 ∧ p7) → (p7 → p3)))) ∨ ((((p7 → False) ∧ (p7 → p6)) → False) ∨ (((False ∧ p3) ∨ (p0 ∨ p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p7 p0 p2 p3 : Prop)
theorem file81_96724 : (((((p2 → p0) → (p7 → False)) → False) ∧ (((True → False) ∧ (False ∧ p3)) ∧ ((p2 → p0) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p3 p6 p2 p0 p7 : Prop)
theorem file81_97178 : (((((p7 ∧ False) → (p2 → p3)) → ((False ∧ p6) → (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p7 ∧ False) → (p2 → p3)) → ((False ∧ p6) → (p0 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p2 p0 p3 p6 : Prop)
theorem file81_97634 : ((((((False → p3) → False) → ((p3 → False) ∨ (True ∧ p2))) → False) ∧ ((((p0 ∨ p3) ∨ (True ∧ p2)) ∨ ((p6 ∧ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p0 ∨ p3) ∨ (True ∧ p2)) ∨ ((p6 ∧ p0) → False)) := by
      apply Or.inr
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        have assump_26 : (((p0 ∨ p3) ∨ (True ∧ p2)) ∨ ((p6 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_18 := assump_3 assump_26
        apply False.elim assump_18
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p3 p5 p4 p0 : Prop)
theorem file81_98404 : ((((((p3 ∨ True) → (p5 → False)) → ((p3 ∧ p5) → (True → False))) ∨ (((p4 → False) → (p0 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p3 ∨ True) → (p5 → False)) → ((p3 ∧ p5) → (True → False))) ∨ (((p4 → False) → (p0 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_27 : (p3 ∨ True) := by
        apply Or.inl
        exact assump_10
      let assump_18 := assump_5 assump_27
      have assump_28 : p5 := by
        exact assump_11
      let assump_19 := assump_18 assump_28
      apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p6 p7 p5 p2 : Prop)
theorem file81_99194 : ((((((p6 ∧ False) ∨ (False ∧ p2)) ∨ ((p5 ∨ p2) ∧ (False ∨ True))) ∨ (((False ∨ True) ∧ (p2 ∨ p7)) ∨ ((p2 ∧ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p6 ∧ False) ∨ (False ∧ p2)) ∨ ((p5 ∨ p2) ∧ (False ∨ True))) ∨ (((False ∨ True) ∧ (p2 ∨ p7)) ∨ ((p2 ∧ p5) → False))) := by
    apply Or.inr
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_22 : ((((p6 ∧ False) ∨ (False ∧ p2)) ∨ ((p5 ∨ p2) ∧ (False ∨ True))) ∨ (((False ∨ True) ∧ (p2 ∨ p7)) ∨ ((p2 ∧ p5) → False))) := by
        apply Or.inl
        apply Or.inr
        apply And.intro
        apply Or.inl
        exact assump_7
        apply Or.inr
        apply True.intro
      let assump_14 := assump_1 assump_22
      apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p3 p1 p5 : Prop)
theorem file81_100109 : (((((True → False) → False) ∧ ((p5 ∨ True) ∧ (p3 ∧ p1))) → False) → ((((False → False) → False) → False) ∧ (((p4 ∧ p4) ∧ (p5 ∧ False)) → False))) := by
  intro assump_7
  apply And.intro
  intro assump_8
  have assump_43 : (False → False) := by
    intro assump_22
    apply False.elim assump_22
  let assump_21 := assump_8 assump_43
  apply False.elim assump_21
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_29
    case intro assump_31 assump_32 =>
      cases assump_30
      case intro assump_37 assump_38 =>
        apply False.elim assump_38


variable (p5 p6 p4 p2 p1 p0 : Prop)
theorem file81_100759 : ((((((p2 ∧ True) ∨ (p1 → False)) → False) ∧ (((p0 ∨ p0) → False) ∧ ((p4 → p5) → False))) ∧ ((((p4 ∧ True) ∧ (p2 ∧ p4)) ∧ ((p1 → False) ∧ (p6 → False))) ∧ (((p1 ∨ p2) ∨ (p5 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case intro assump_26 assump_27 =>
                  cases assump_17
                  case intro assump_32 assump_33 =>
                    have assump_44 : ((p1 ∨ p2) ∨ (p5 → False)) := by
                      apply Or.inl
                      apply Or.inr
                      exact assump_26
                    let assump_40 := assump_15 assump_44
                    apply False.elim assump_40


variable (p1 p2 p7 p0 p3 p5 p4 p6 : Prop)
theorem file81_101952 : ((((((p0 ∧ p1) ∧ (p4 ∧ p4)) ∨ ((p7 ∧ p0) ∧ (True → p0))) ∨ (((p1 ∨ True) ∧ (p7 → p7)) ∧ ((p4 → False) → (True → False)))) ∧ ((((p6 → False) → False) ∧ ((p5 ∧ False) ∨ (False ∧ True))) ∧ (((p3 ∧ p1) ∧ (p2 ∨ p6)) → ((p1 ∨ p6) → False)))) → False) := by
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
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case inl assump_28 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_31
                  case inr assump_29 =>
                    cases assump_29
                    case intro assump_36 assump_37 =>
                      apply False.elim assump_36
      case inr assump_7 =>
        cases assump_7
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            cases assump_3
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_53
                case inl assump_56 =>
                  cases assump_56
                  case intro assump_58 assump_59 =>
                    apply False.elim assump_59
                case inr assump_57 =>
                  cases assump_57
                  case intro assump_64 assump_65 =>
                    apply False.elim assump_64
    case inr assump_5 =>
      cases assump_5
      case intro assump_68 assump_69 =>
        cases assump_68
        case intro assump_70 assump_71 =>
          cases assump_70
          case inl assump_72 =>
            cases assump_3
            case intro assump_80 assump_81 =>
              cases assump_80
              case intro assump_82 assump_83 =>
                cases assump_83
                case inl assump_86 =>
                  cases assump_86
                  case intro assump_88 assump_89 =>
                    apply False.elim assump_89
                case inr assump_87 =>
                  cases assump_87
                  case intro assump_94 assump_95 =>
                    apply False.elim assump_94
          case inr assump_73 =>
            cases assump_3
            case intro assump_104 assump_105 =>
              cases assump_104
              case intro assump_106 assump_107 =>
                cases assump_107
                case inl assump_110 =>
                  cases assump_110
                  case intro assump_112 assump_113 =>
                    apply False.elim assump_113
                case inr assump_111 =>
                  cases assump_111
                  case intro assump_118 assump_119 =>
                    apply False.elim assump_118


variable (p4 p1 p6 p5 p7 : Prop)
theorem file81_105171 : ((((((p4 → False) ∧ (p5 → False)) ∧ ((p7 ∧ p6) ∨ (p4 → False))) → False) ∧ ((((True ∧ False) ∨ (p1 ∧ False)) → False) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    have assump_35 : (((True ∧ False) ∨ (p1 ∧ False)) → False) := by
      intro assump_17
      cases assump_17
      case inl assump_18 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
      case inr assump_19 =>
        cases assump_19
        case intro assump_26 assump_27 =>
          apply False.elim assump_27
    let assump_16 := assump_11 assump_35
    apply False.elim assump_16


variable (p3 p0 p2 p4 p1 p7 p5 p6 : Prop)
theorem file81_105897 : (((((p2 ∧ p3) → (p1 ∨ True)) ∧ ((p0 → False) ∧ (p6 ∧ False))) → False) ∨ ((((p1 → p4) → (p5 ∨ p7)) → ((False ∨ p2) ∨ (p4 ∨ True))) ∨ (((p0 → False) ∨ (p5 ∨ p0)) ∧ ((p1 → False) ∨ (p0 ∧ True))))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_15


variable (p0 p7 p1 : Prop)
theorem file81_106386 : ((((((True ∨ p1) → False) ∧ ((p7 → p1) ∨ (p7 → p0))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((True ∨ p1) → False) ∧ ((p7 → p1) ∨ (p7 → p0))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_30 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_15 := assump_6 assump_30
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_31 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_22 := assump_6 assump_31
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p5 p0 p2 p4 : Prop)
theorem file81_107188 : ((((((p5 → p5) ∨ (p0 → p5)) ∨ ((p2 ∨ p4) ∨ (p4 → False))) ∧ (((p0 → p0) ∨ (p5 ∨ p4)) → False)) ∧ ((((True ∨ p2) → (p5 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_109 : (((True ∨ p2) → (p5 ∧ False)) → False) := by
            intro assump_17
            have assump_110 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_20 := assump_17 assump_110
            let assump_21 := And.right assump_20
            apply False.elim assump_21
          let assump_16 := assump_3 assump_109
          apply False.elim assump_16
        case inr assump_9 =>
          have assump_111 : (((True ∨ p2) → (p5 ∧ False)) → False) := by
            intro assump_36
            have assump_112 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_39 := assump_36 assump_112
            let assump_40 := And.right assump_39
            apply False.elim assump_40
          let assump_35 := assump_3 assump_111
          apply False.elim assump_35
      case inr assump_7 =>
        cases assump_7
        case inl assump_48 =>
          cases assump_48
          case inl assump_50 =>
            have assump_113 : (((True ∨ p2) → (p5 ∧ False)) → False) := by
              intro assump_59
              have assump_114 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_62 := assump_59 assump_114
              let assump_63 := And.right assump_62
              apply False.elim assump_63
            let assump_58 := assump_3 assump_113
            apply False.elim assump_58
          case inr assump_51 =>
            have assump_115 : (((True ∨ p2) → (p5 ∧ False)) → False) := by
              intro assump_78
              have assump_116 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_81 := assump_78 assump_116
              let assump_82 := And.right assump_81
              apply False.elim assump_82
            let assump_77 := assump_3 assump_115
            apply False.elim assump_77
        case inr assump_49 =>
          have assump_117 : (((True ∨ p2) → (p5 ∧ False)) → False) := by
            intro assump_97
            have assump_118 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_100 := assump_97 assump_118
            let assump_101 := And.right assump_100
            apply False.elim assump_101
          let assump_96 := assump_3 assump_117
          apply False.elim assump_96


variable (p2 p0 p4 p3 : Prop)
theorem file81_110045 : (((((p3 → p3) → False) → False) → False) → ((((p2 → p4) ∧ (p2 ∨ p0)) → False) ∨ (((p2 ∧ False) → False) ∧ ((p4 ∧ p3) → (p0 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_48 : (((p3 → p3) → False) → False) := by
        intro assump_17
        have assump_49 : (p3 → p3) := by
          intro assump_21
          exact assump_21
        let assump_20 := assump_17 assump_49
        apply False.elim assump_20
      let assump_16 := assump_1 assump_48
      apply False.elim assump_16
    case inr assump_10 =>
      have assump_50 : (((p3 → p3) → False) → False) := by
        intro assump_35
        have assump_51 : (p3 → p3) := by
          intro assump_39
          exact assump_39
        let assump_38 := assump_35 assump_51
        apply False.elim assump_38
      let assump_34 := assump_1 assump_50
      apply False.elim assump_34


