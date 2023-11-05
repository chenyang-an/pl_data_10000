variable (p5 p0 p1 p4 p2 p3 p6 : Prop)
theorem file86_47 : ((((((p3 ∧ p4) → False) → ((p3 → False) → (p0 ∨ p5))) → (((p5 → False) → (p5 → p6)) → ((p3 ∧ p1) ∨ (p2 → p2)))) ∧ ((((True ∧ p4) → False) ∧ ((p3 ∧ p5) ∧ (True → False))) ∧ (((p1 ∧ p4) ∧ (p3 → False)) ∨ ((p5 ∧ False) ∧ (True → False))))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_7
            case inl assump_22 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  have assump_46 : p3 := by
                    exact assump_14
                  let assump_34 := assump_25 assump_46
                  apply False.elim assump_34
            case inr assump_23 =>
              cases assump_23
              case intro assump_38 assump_39 =>
                cases assump_38
                case intro assump_40 assump_41 =>
                  apply False.elim assump_41


variable (p1 p6 p0 p3 p7 : Prop)
theorem file86_1313 : ((((((True → False) → False) ∨ ((p1 ∨ p0) → (p6 ∨ False))) ∨ (((p7 → p3) → False) ∧ ((p6 ∧ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True → False) → False) ∨ ((p1 ∨ p0) → (p6 ∨ False))) ∨ (((p7 → p3) → False) ∧ ((p6 ∧ p7) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p5 p1 : Prop)
theorem file86_1882 : ((((((p5 ∧ p3) ∨ (p1 → p5)) → False) → False) ∧ ((((p3 → True) → False) → ((False → True) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p3 → True) → False) → ((False → True) → False)) := by
      intro assump_9
      intro assump_10
      have assump_24 : (p3 → True) := by
        intro assump_16
        apply True.intro
      let assump_15 := assump_9 assump_24
      apply False.elim assump_15
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p2 p7 p4 p0 p5 p1 p3 p6 : Prop)
theorem file86_2496 : ((((((p4 ∧ True) → (p1 → p5)) → False) → (((p6 ∨ p7) ∧ (False → p5)) → False)) ∧ ((((p5 ∧ p5) ∧ (p4 ∨ p3)) ∧ ((p2 ∨ False) ∧ (False ∧ False))) ∧ (((True ∨ p5) ∨ (p0 ∧ p4)) ∧ ((p0 ∧ False) → (p4 → False))))) → False) := by
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
            cases assump_11
            case inl assump_18 =>
              cases assump_9
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_23
                  case intro assump_28 assump_29 =>
                    apply False.elim assump_28
                case inr assump_25 =>
                  apply False.elim assump_25
            case inr assump_19 =>
              cases assump_9
              case intro assump_36 assump_37 =>
                cases assump_36
                case inl assump_38 =>
                  cases assump_37
                  case intro assump_42 assump_43 =>
                    apply False.elim assump_42
                case inr assump_39 =>
                  apply False.elim assump_39


variable (p5 p7 p2 p1 p0 p3 p6 p4 : Prop)
theorem file86_3923 : ((((((p5 ∨ p0) ∨ (p2 → False)) ∧ ((True ∨ False) ∨ (p5 → False))) ∧ (((p0 → p1) → False) ∨ ((p5 → p2) → (p6 → False)))) ∧ ((((p4 ∨ p0) → False) ∨ ((True ∧ p1) ∧ (p0 ∧ False))) ∧ (((p7 ∧ p3) → (False → True)) ∧ ((True ∧ p0) ∧ (True → p2))))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_13
            case inl assump_20 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_11
                case inl assump_26 =>
                  cases assump_9
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case inl assump_32 =>
                      cases assump_31
                      case intro assump_36 assump_37 =>
                        cases assump_37
                        case intro assump_40 assump_41 =>
                          cases assump_40
                          case intro assump_42 assump_43 =>
                            have assump_594 : (p4 ∨ p0) := by
                              apply Or.inr
                              exact assump_43
                            let assump_54 := assump_32 assump_594
                            apply False.elim assump_54
                    case inr assump_33 =>
                      cases assump_33
                      case intro assump_58 assump_59 =>
                        cases assump_58
                        case intro assump_60 assump_61 =>
                          cases assump_59
                          case intro assump_66 assump_67 =>
                            apply False.elim assump_67
                case inr assump_27 =>
                  cases assump_9
                  case intro assump_74 assump_75 =>
                    cases assump_74
                    case inl assump_76 =>
                      cases assump_75
                      case intro assump_80 assump_81 =>
                        cases assump_81
                        case intro assump_84 assump_85 =>
                          cases assump_84
                          case intro assump_86 assump_87 =>
                            have assump_595 : (p4 ∨ p0) := by
                              apply Or.inr
                              exact assump_87
                            let assump_98 := assump_76 assump_595
                            apply False.elim assump_98
                    case inr assump_77 =>
                      cases assump_77
                      case intro assump_102 assump_103 =>
                        cases assump_102
                        case intro assump_104 assump_105 =>
                          cases assump_103
                          case intro assump_110 assump_111 =>
                            apply False.elim assump_111
              case inr assump_23 =>
                apply False.elim assump_23
            case inr assump_21 =>
              cases assump_11
              case inl assump_120 =>
                cases assump_9
                case intro assump_124 assump_125 =>
                  cases assump_124
                  case inl assump_126 =>
                    cases assump_125
                    case intro assump_130 assump_131 =>
                      cases assump_131
                      case intro assump_134 assump_135 =>
                        cases assump_134
                        case intro assump_136 assump_137 =>
                          have assump_596 : (p4 ∨ p0) := by
                            apply Or.inr
                            exact assump_137
                          let assump_148 := assump_126 assump_596
                          apply False.elim assump_148
                  case inr assump_127 =>
                    cases assump_127
                    case intro assump_152 assump_153 =>
                      cases assump_152
                      case intro assump_154 assump_155 =>
                        cases assump_153
                        case intro assump_160 assump_161 =>
                          apply False.elim assump_161
              case inr assump_121 =>
                cases assump_9
                case intro assump_168 assump_169 =>
                  cases assump_168
                  case inl assump_170 =>
                    cases assump_169
                    case intro assump_174 assump_175 =>
                      cases assump_175
                      case intro assump_178 assump_179 =>
                        cases assump_178
                        case intro assump_180 assump_181 =>
                          have assump_597 : (p4 ∨ p0) := by
                            apply Or.inr
                            exact assump_181
                          let assump_192 := assump_170 assump_597
                          apply False.elim assump_192
                  case inr assump_171 =>
                    cases assump_171
                    case intro assump_196 assump_197 =>
                      cases assump_196
                      case intro assump_198 assump_199 =>
                        cases assump_197
                        case intro assump_204 assump_205 =>
                          apply False.elim assump_205
          case inr assump_17 =>
            cases assump_13
            case inl assump_212 =>
              cases assump_212
              case inl assump_214 =>
                cases assump_11
                case inl assump_218 =>
                  cases assump_9
                  case intro assump_222 assump_223 =>
                    cases assump_222
                    case inl assump_224 =>
                      cases assump_223
                      case intro assump_228 assump_229 =>
                        cases assump_229
                        case intro assump_232 assump_233 =>
                          cases assump_232
                          case intro assump_234 assump_235 =>
                            have assump_598 : (p4 ∨ p0) := by
                              apply Or.inr
                              exact assump_235
                            let assump_246 := assump_224 assump_598
                            apply False.elim assump_246
                    case inr assump_225 =>
                      cases assump_225
                      case intro assump_250 assump_251 =>
                        cases assump_250
                        case intro assump_252 assump_253 =>
                          cases assump_251
                          case intro assump_258 assump_259 =>
                            apply False.elim assump_259
                case inr assump_219 =>
                  cases assump_9
                  case intro assump_266 assump_267 =>
                    cases assump_266
                    case inl assump_268 =>
                      cases assump_267
                      case intro assump_272 assump_273 =>
                        cases assump_273
                        case intro assump_276 assump_277 =>
                          cases assump_276
                          case intro assump_278 assump_279 =>
                            have assump_599 : (p4 ∨ p0) := by
                              apply Or.inr
                              exact assump_279
                            let assump_290 := assump_268 assump_599
                            apply False.elim assump_290
                    case inr assump_269 =>
                      cases assump_269
                      case intro assump_294 assump_295 =>
                        cases assump_294
                        case intro assump_296 assump_297 =>
                          cases assump_295
                          case intro assump_302 assump_303 =>
                            apply False.elim assump_303
              case inr assump_215 =>
                apply False.elim assump_215
            case inr assump_213 =>
              cases assump_11
              case inl assump_312 =>
                cases assump_9
                case intro assump_316 assump_317 =>
                  cases assump_316
                  case inl assump_318 =>
                    cases assump_317
                    case intro assump_322 assump_323 =>
                      cases assump_323
                      case intro assump_326 assump_327 =>
                        cases assump_326
                        case intro assump_328 assump_329 =>
                          have assump_600 : (p4 ∨ p0) := by
                            apply Or.inr
                            exact assump_329
                          let assump_340 := assump_318 assump_600
                          apply False.elim assump_340
                  case inr assump_319 =>
                    cases assump_319
                    case intro assump_344 assump_345 =>
                      cases assump_344
                      case intro assump_346 assump_347 =>
                        cases assump_345
                        case intro assump_352 assump_353 =>
                          apply False.elim assump_353
              case inr assump_313 =>
                cases assump_9
                case intro assump_360 assump_361 =>
                  cases assump_360
                  case inl assump_362 =>
                    cases assump_361
                    case intro assump_366 assump_367 =>
                      cases assump_367
                      case intro assump_370 assump_371 =>
                        cases assump_370
                        case intro assump_372 assump_373 =>
                          have assump_601 : (p4 ∨ p0) := by
                            apply Or.inr
                            exact assump_373
                          let assump_384 := assump_362 assump_601
                          apply False.elim assump_384
                  case inr assump_363 =>
                    cases assump_363
                    case intro assump_388 assump_389 =>
                      cases assump_388
                      case intro assump_390 assump_391 =>
                        cases assump_389
                        case intro assump_396 assump_397 =>
                          apply False.elim assump_397
        case inr assump_15 =>
          cases assump_13
          case inl assump_404 =>
            cases assump_404
            case inl assump_406 =>
              cases assump_11
              case inl assump_410 =>
                cases assump_9
                case intro assump_414 assump_415 =>
                  cases assump_414
                  case inl assump_416 =>
                    cases assump_415
                    case intro assump_420 assump_421 =>
                      cases assump_421
                      case intro assump_424 assump_425 =>
                        cases assump_424
                        case intro assump_426 assump_427 =>
                          have assump_602 : (p4 ∨ p0) := by
                            apply Or.inr
                            exact assump_427
                          let assump_438 := assump_416 assump_602
                          apply False.elim assump_438
                  case inr assump_417 =>
                    cases assump_417
                    case intro assump_442 assump_443 =>
                      cases assump_442
                      case intro assump_444 assump_445 =>
                        cases assump_443
                        case intro assump_450 assump_451 =>
                          apply False.elim assump_451
              case inr assump_411 =>
                cases assump_9
                case intro assump_458 assump_459 =>
                  cases assump_458
                  case inl assump_460 =>
                    cases assump_459
                    case intro assump_464 assump_465 =>
                      cases assump_465
                      case intro assump_468 assump_469 =>
                        cases assump_468
                        case intro assump_470 assump_471 =>
                          have assump_603 : (p4 ∨ p0) := by
                            apply Or.inr
                            exact assump_471
                          let assump_482 := assump_460 assump_603
                          apply False.elim assump_482
                  case inr assump_461 =>
                    cases assump_461
                    case intro assump_486 assump_487 =>
                      cases assump_486
                      case intro assump_488 assump_489 =>
                        cases assump_487
                        case intro assump_494 assump_495 =>
                          apply False.elim assump_495
            case inr assump_407 =>
              apply False.elim assump_407
          case inr assump_405 =>
            cases assump_11
            case inl assump_504 =>
              cases assump_9
              case intro assump_508 assump_509 =>
                cases assump_508
                case inl assump_510 =>
                  cases assump_509
                  case intro assump_514 assump_515 =>
                    cases assump_515
                    case intro assump_518 assump_519 =>
                      cases assump_518
                      case intro assump_520 assump_521 =>
                        have assump_604 : (p4 ∨ p0) := by
                          apply Or.inr
                          exact assump_521
                        let assump_532 := assump_510 assump_604
                        apply False.elim assump_532
                case inr assump_511 =>
                  cases assump_511
                  case intro assump_536 assump_537 =>
                    cases assump_536
                    case intro assump_538 assump_539 =>
                      cases assump_537
                      case intro assump_544 assump_545 =>
                        apply False.elim assump_545
            case inr assump_505 =>
              cases assump_9
              case intro assump_552 assump_553 =>
                cases assump_552
                case inl assump_554 =>
                  cases assump_553
                  case intro assump_558 assump_559 =>
                    cases assump_559
                    case intro assump_562 assump_563 =>
                      cases assump_562
                      case intro assump_564 assump_565 =>
                        have assump_605 : (p4 ∨ p0) := by
                          apply Or.inr
                          exact assump_565
                        let assump_576 := assump_554 assump_605
                        apply False.elim assump_576
                case inr assump_555 =>
                  cases assump_555
                  case intro assump_580 assump_581 =>
                    cases assump_580
                    case intro assump_582 assump_583 =>
                      cases assump_581
                      case intro assump_588 assump_589 =>
                        apply False.elim assump_589


variable (p2 p7 p0 p5 p4 p1 : Prop)
theorem file86_19218 : ((((((p1 → False) → False) → ((p0 → False) → False)) ∨ (((False ∧ p2) → False) → ((p5 ∧ p4) ∧ (p0 ∨ p7)))) ∧ ((((p2 ∧ p0) ∧ (p2 ∧ True)) ∧ ((p1 → p2) ∧ (p4 ∧ p5))) ∧ (((p5 → False) → (p0 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_13
              case intro assump_20 assump_21 =>
                cases assump_11
                case intro assump_26 assump_27 =>
                  cases assump_27
                  case intro assump_30 assump_31 =>
                    have assump_82 : ((p5 → False) → (p0 → True)) := by
                      intro assump_39
                      intro assump_40
                      apply True.intro
                    let assump_38 := assump_9 assump_82
                    apply False.elim assump_38
    case inr assump_5 =>
      cases assump_3
      case intro assump_46 assump_47 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_51
              case intro assump_58 assump_59 =>
                cases assump_49
                case intro assump_64 assump_65 =>
                  cases assump_65
                  case intro assump_68 assump_69 =>
                    have assump_83 : ((p5 → False) → (p0 → True)) := by
                      intro assump_77
                      intro assump_78
                      apply True.intro
                    let assump_76 := assump_47 assump_83
                    apply False.elim assump_76


variable (p0 p7 p6 p1 p3 : Prop)
theorem file86_21246 : (((((False → False) → False) ∧ ((p0 → False) ∨ (p3 → p6))) → (((p7 → False) → False) ∧ ((True ∧ True) ∧ (p1 → False)))) ∨ ((((p0 → p7) → False) → False) ∧ (((p1 → p0) → False) → False))) := by
  apply Or.inl
  intro assump_19
  apply And.intro
  intro assump_20
  cases assump_19
  case intro assump_23 assump_24 =>
    cases assump_24
    case inl assump_27 =>
      have assump_78 : (False → False) := by
        intro assump_33
        apply False.elim assump_33
      let assump_32 := assump_23 assump_78
      apply False.elim assump_32
    case inr assump_28 =>
      have assump_79 : (False → False) := by
        intro assump_43
        apply False.elim assump_43
      let assump_42 := assump_23 assump_79
      apply False.elim assump_42
  apply And.intro
  apply And.intro
  apply True.intro
  apply True.intro
  intro assump_49
  cases assump_19
  case intro assump_52 assump_53 =>
    cases assump_53
    case inl assump_56 =>
      have assump_80 : (False → False) := by
        intro assump_62
        apply False.elim assump_62
      let assump_61 := assump_52 assump_80
      apply False.elim assump_61
    case inr assump_57 =>
      have assump_81 : (False → False) := by
        intro assump_72
        apply False.elim assump_72
      let assump_71 := assump_52 assump_81
      apply False.elim assump_71


variable (p0 p4 p6 p1 p3 p2 p7 p5 : Prop)
theorem file86_22638 : (((((p4 → False) ∨ (p4 ∧ p5)) → ((p2 ∧ p4) → (p4 ∧ p0))) → (((True → False) → (p0 → False)) ∨ ((p1 ∧ False) → False))) ∨ ((((p6 → True) ∧ (p0 → False)) → ((False → p7) ∧ (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_5
  apply Or.inl
  intro assump_8
  intro assump_9
  have assump_18 : True := by
    apply True.intro
  let assump_14 := assump_8 assump_18
  apply False.elim assump_14


variable (p2 p6 p1 p5 p3 p4 : Prop)
theorem file86_23098 : (((((p2 ∧ False) → (p6 ∧ p4)) ∨ ((p1 → False) → (p4 ∨ p5))) → (((p4 ∨ True) → False) ∧ ((True ∧ p6) ∧ (p2 → p3)))) → False) := by
  intro assump_1
  have assump_23 : (((p2 ∧ False) → (p6 ∧ p4)) ∨ ((p1 → False) → (p4 ∨ p5))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  let assump_4 := assump_1 assump_23
  let assump_18 := And.left assump_4
  have assump_24 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_19 := assump_18 assump_24
  apply False.elim assump_19


variable (p0 p2 p5 p7 p4 p6 : Prop)
theorem file86_23838 : (((((p6 → p6) ∨ (p4 → p0)) ∨ ((p6 → False) ∧ (p0 ∧ p7))) → (((p2 → p7) → (p5 ∧ p6)) → ((p5 ∧ False) → (p7 → False)))) ∨ ((((p6 ∨ p6) → False) → ((True → p5) ∨ (False ∨ p6))) ∧ (((True → p4) → (True ∨ True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    apply False.elim assump_8


variable (p3 p6 p5 p2 p0 p4 : Prop)
theorem file86_24286 : ((((((p0 → False) ∧ (p6 → p6)) ∨ ((p5 → False) → False)) → (((False → False) ∧ (p0 ∨ True)) ∧ ((p2 → p2) ∨ (False → p5)))) → ((((False → False) ∨ (p4 → p4)) → False) ∧ (((p2 → p3) → False) → False))) → False) := by
  intro assump_1
  have assump_43 : ((((p0 → False) ∧ (p6 → p6)) ∨ ((p5 → False) → False)) → (((False → False) ∧ (p0 ∨ True)) ∧ ((p2 → p2) ∨ (False → p5)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inr
        apply True.intro
    case inr assump_10 =>
      apply Or.inr
      apply True.intro
    cases assump_5
    case inl assump_19 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        apply Or.inl
        intro assump_27
        exact assump_27
    case inr assump_20 =>
      apply Or.inl
      intro assump_32
      exact assump_32
  let assump_4 := assump_1 assump_43
  let assump_35 := And.left assump_4
  have assump_44 : ((False → False) ∨ (p4 → p4)) := by
    apply Or.inl
    intro assump_37
    apply False.elim assump_37
  let assump_36 := assump_35 assump_44
  apply False.elim assump_36


variable (p0 p3 p7 p2 p5 : Prop)
theorem file86_25578 : ((((((p3 → False) → (p5 ∨ p2)) ∨ ((p2 ∧ p7) ∨ (p0 → p0))) → False) ∧ ((((p0 → p2) → (p3 → True)) ∨ ((p0 ∨ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_14 : (((p0 → p2) → (p3 → True)) ∨ ((p0 ∨ p0) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_3 assump_14
    apply False.elim assump_8


variable (p2 p6 p7 p4 p5 p1 : Prop)
theorem file86_26082 : ((((((p1 → p4) ∨ (False ∨ p4)) ∨ ((p2 → False) ∧ (p7 ∨ p5))) ∧ (((p5 ∧ p6) ∧ (True → False)) ∧ ((p4 ∨ p5) → (p5 ∧ p4)))) ∨ ((((True → False) ∧ (p1 → p6)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_14
              case intro assump_16 assump_17 =>
                have assump_134 : True := by
                  apply True.intro
                let assump_30 := assump_15 assump_134
                apply False.elim assump_30
        case inr assump_9 =>
          cases assump_9
          case inl assump_34 =>
            apply False.elim assump_34
          case inr assump_35 =>
            cases assump_5
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  have assump_135 : True := by
                    apply True.intro
                  let assump_58 := assump_43 assump_135
                  apply False.elim assump_58
      case inr assump_7 =>
        cases assump_7
        case intro assump_62 assump_63 =>
          cases assump_63
          case inl assump_66 =>
            cases assump_5
            case intro assump_70 assump_71 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                cases assump_72
                case intro assump_74 assump_75 =>
                  have assump_136 : True := by
                    apply True.intro
                  let assump_88 := assump_73 assump_136
                  apply False.elim assump_88
          case inr assump_67 =>
            cases assump_5
            case intro assump_94 assump_95 =>
              cases assump_94
              case intro assump_96 assump_97 =>
                cases assump_96
                case intro assump_98 assump_99 =>
                  have assump_137 : True := by
                    apply True.intro
                  let assump_112 := assump_97 assump_137
                  apply False.elim assump_112
  case inr assump_3 =>
    have assump_138 : (((True → False) ∧ (p1 → p6)) → False) := by
      intro assump_119
      cases assump_119
      case intro assump_120 assump_121 =>
        have assump_139 : True := by
          apply True.intro
        let assump_127 := assump_120 assump_139
        apply False.elim assump_127
    let assump_118 := assump_3 assump_138
    apply False.elim assump_118


variable (p5 p0 p4 p6 p1 p3 p2 : Prop)
theorem file86_28938 : (((((p5 → False) → False) → False) → (((p2 → False) → False) → ((p5 → False) ∨ (p0 → False)))) ∨ ((((p1 → p2) ∧ (p3 ∧ p0)) ∨ ((p5 ∨ p2) → False)) ∧ (((p6 → p0) ∧ (p5 → False)) → ((p3 → p4) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_22 : ((p5 → False) → False) := by
    intro assump_12
    have assump_23 : p5 := by
      exact assump_7
    let assump_15 := assump_12 assump_23
    apply False.elim assump_15
  let assump_11 := assump_1 assump_22
  apply False.elim assump_11


variable (p1 p0 p4 p6 p7 p5 p2 p3 : Prop)
theorem file86_29550 : (((((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) → False) → ((((p6 ∨ True) → False) ∧ ((p0 ∨ p3) ∧ (p1 ∧ p2))) ∧ (((p2 → False) → (p3 → p5)) ∧ ((p4 ∨ p1) ∨ (False ∧ p0))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_239 : (((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) := by
      intro assump_10
      intro assump_11
      cases assump_10
      case inl assump_14 =>
        apply Or.inr
        exact assump_3
      case inr assump_15 =>
        cases assump_15
        case inl assump_18 =>
          apply Or.inr
          exact assump_3
        case inr assump_19 =>
          apply Or.inr
          exact assump_3
    let assump_9 := assump_1 assump_239
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_240 : (((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) := by
      intro assump_32
      intro assump_33
      cases assump_32
      case inl assump_36 =>
        have assump_241 : True := by
          apply True.intro
        let assump_41 := assump_33 assump_241
        apply False.elim assump_41
      case inr assump_37 =>
        cases assump_37
        case inl assump_45 =>
          have assump_242 : True := by
            apply True.intro
          let assump_49 := assump_33 assump_242
          apply False.elim assump_49
        case inr assump_46 =>
          have assump_243 : True := by
            apply True.intro
          let assump_56 := assump_33 assump_243
          apply False.elim assump_56
    let assump_31 := assump_1 assump_240
    apply False.elim assump_31
  apply And.intro
  have assump_244 : (((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) := by
    intro assump_66
    intro assump_67
    cases assump_66
    case inl assump_70 =>
      have assump_245 : True := by
        apply True.intro
      let assump_75 := assump_67 assump_245
      apply False.elim assump_75
    case inr assump_71 =>
      cases assump_71
      case inl assump_79 =>
        have assump_246 : True := by
          apply True.intro
        let assump_83 := assump_67 assump_246
        apply False.elim assump_83
      case inr assump_80 =>
        have assump_247 : True := by
          apply True.intro
        let assump_90 := assump_67 assump_247
        apply False.elim assump_90
  let assump_65 := assump_1 assump_244
  apply False.elim assump_65
  apply And.intro
  have assump_248 : (((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) := by
    intro assump_100
    intro assump_101
    cases assump_100
    case inl assump_104 =>
      have assump_249 : True := by
        apply True.intro
      let assump_109 := assump_101 assump_249
      apply False.elim assump_109
    case inr assump_105 =>
      cases assump_105
      case inl assump_113 =>
        have assump_250 : True := by
          apply True.intro
        let assump_117 := assump_101 assump_250
        apply False.elim assump_117
      case inr assump_114 =>
        have assump_251 : True := by
          apply True.intro
        let assump_124 := assump_101 assump_251
        apply False.elim assump_124
  let assump_99 := assump_1 assump_248
  apply False.elim assump_99
  have assump_252 : (((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) := by
    intro assump_134
    intro assump_135
    cases assump_134
    case inl assump_138 =>
      have assump_253 : True := by
        apply True.intro
      let assump_143 := assump_135 assump_253
      apply False.elim assump_143
    case inr assump_139 =>
      cases assump_139
      case inl assump_147 =>
        have assump_254 : True := by
          apply True.intro
        let assump_151 := assump_135 assump_254
        apply False.elim assump_151
      case inr assump_148 =>
        have assump_255 : True := by
          apply True.intro
        let assump_158 := assump_135 assump_255
        apply False.elim assump_158
  let assump_133 := assump_1 assump_252
  apply False.elim assump_133
  apply And.intro
  intro assump_165
  intro assump_166
  have assump_256 : (((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) := by
    intro assump_174
    intro assump_175
    cases assump_174
    case inl assump_178 =>
      have assump_257 : True := by
        apply True.intro
      let assump_183 := assump_175 assump_257
      apply False.elim assump_183
    case inr assump_179 =>
      cases assump_179
      case inl assump_187 =>
        have assump_258 : True := by
          apply True.intro
        let assump_191 := assump_175 assump_258
        apply False.elim assump_191
      case inr assump_188 =>
        have assump_259 : True := by
          apply True.intro
        let assump_198 := assump_175 assump_259
        apply False.elim assump_198
  let assump_173 := assump_1 assump_256
  apply False.elim assump_173
  have assump_260 : (((p5 → False) ∨ (True ∨ p2)) → ((True → False) → (p7 ∨ p6))) := by
    intro assump_208
    intro assump_209
    cases assump_208
    case inl assump_212 =>
      have assump_261 : True := by
        apply True.intro
      let assump_217 := assump_209 assump_261
      apply False.elim assump_217
    case inr assump_213 =>
      cases assump_213
      case inl assump_221 =>
        have assump_262 : True := by
          apply True.intro
        let assump_225 := assump_209 assump_262
        apply False.elim assump_225
      case inr assump_222 =>
        have assump_263 : True := by
          apply True.intro
        let assump_232 := assump_209 assump_263
        apply False.elim assump_232
  let assump_207 := assump_1 assump_260
  apply False.elim assump_207


variable (p7 p6 p3 p4 p0 p5 p1 : Prop)
theorem file86_35296 : (((((p0 ∨ p0) → (p5 ∨ p1)) ∧ ((p1 ∨ p6) → (p1 ∧ p4))) → (((p6 → False) ∧ (p3 ∧ False)) → False)) ∨ ((((p5 ∧ p4) ∧ (p1 → p7)) → False) → (((p4 → True) → False) → ((True ∧ True) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p1 p2 p4 p7 p0 p6 : Prop)
theorem file86_35737 : (((((False ∧ p2) → (p2 ∧ False)) → False) ∧ (((p1 ∨ p6) ∧ (p6 ∧ p0)) ∨ ((p4 ∨ p7) ∧ (p2 → False)))) → ((((p1 → False) ∧ (True ∧ True)) → False) → (((p0 → False) → False) → ((True → True) ∧ (p4 ∧ p2))))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  apply And.intro
  intro assump_8
  apply True.intro
  apply And.intro
  cases assump_5
  case intro assump_13 assump_14 =>
    cases assump_14
    case inl assump_17 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case inl assump_21 =>
          cases assump_20
          case intro assump_25 assump_26 =>
            have assump_202 : ((False ∧ p2) → (p2 ∧ False)) := by
              intro assump_35
              apply And.intro
              cases assump_35
              case intro assump_36 assump_37 =>
                apply False.elim assump_36
              cases assump_35
              case intro assump_40 assump_41 =>
                apply False.elim assump_40
            let assump_34 := assump_13 assump_202
            apply False.elim assump_34
        case inr assump_22 =>
          cases assump_20
          case intro assump_49 assump_50 =>
            have assump_203 : ((False ∧ p2) → (p2 ∧ False)) := by
              intro assump_59
              apply And.intro
              cases assump_59
              case intro assump_60 assump_61 =>
                apply False.elim assump_60
              cases assump_59
              case intro assump_64 assump_65 =>
                apply False.elim assump_64
            let assump_58 := assump_13 assump_203
            apply False.elim assump_58
    case inr assump_18 =>
      cases assump_18
      case intro assump_71 assump_72 =>
        cases assump_71
        case inl assump_73 =>
          exact assump_73
        case inr assump_74 =>
          have assump_204 : ((False ∧ p2) → (p2 ∧ False)) := by
            intro assump_86
            apply And.intro
            cases assump_86
            case intro assump_87 assump_88 =>
              apply False.elim assump_87
            cases assump_86
            case intro assump_91 assump_92 =>
              apply False.elim assump_91
          let assump_85 := assump_13 assump_204
          apply False.elim assump_85
  cases assump_5
  case intro assump_102 assump_103 =>
    cases assump_103
    case inl assump_106 =>
      cases assump_106
      case intro assump_108 assump_109 =>
        cases assump_108
        case inl assump_110 =>
          cases assump_109
          case intro assump_114 assump_115 =>
            have assump_205 : ((False ∧ p2) → (p2 ∧ False)) := by
              intro assump_124
              apply And.intro
              cases assump_124
              case intro assump_125 assump_126 =>
                apply False.elim assump_125
              cases assump_124
              case intro assump_129 assump_130 =>
                apply False.elim assump_129
            let assump_123 := assump_102 assump_205
            apply False.elim assump_123
        case inr assump_111 =>
          cases assump_109
          case intro assump_138 assump_139 =>
            have assump_206 : ((False ∧ p2) → (p2 ∧ False)) := by
              intro assump_148
              apply And.intro
              cases assump_148
              case intro assump_149 assump_150 =>
                apply False.elim assump_149
              cases assump_148
              case intro assump_153 assump_154 =>
                apply False.elim assump_153
            let assump_147 := assump_102 assump_206
            apply False.elim assump_147
    case inr assump_107 =>
      cases assump_107
      case intro assump_160 assump_161 =>
        cases assump_160
        case inl assump_162 =>
          have assump_207 : ((False ∧ p2) → (p2 ∧ False)) := by
            intro assump_171
            apply And.intro
            cases assump_171
            case intro assump_172 assump_173 =>
              apply False.elim assump_172
            cases assump_171
            case intro assump_176 assump_177 =>
              apply False.elim assump_176
          let assump_170 := assump_102 assump_207
          apply False.elim assump_170
        case inr assump_163 =>
          have assump_208 : ((False ∧ p2) → (p2 ∧ False)) := by
            intro assump_190
            apply And.intro
            cases assump_190
            case intro assump_191 assump_192 =>
              apply False.elim assump_191
            cases assump_190
            case intro assump_195 assump_196 =>
              apply False.elim assump_195
          let assump_189 := assump_102 assump_208
          apply False.elim assump_189


variable (p7 p4 p0 p5 p2 : Prop)
theorem file86_40470 : ((((((False → True) ∨ (p0 → p5)) ∨ ((p4 → False) → (p5 ∧ True))) ∧ (((p7 ∧ False) → (p2 ∨ p4)) ∨ ((p5 ∨ p2) → (p5 → p5)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False → True) ∨ (p0 → p5)) ∨ ((p4 → False) → (p5 ∧ True))) ∧ (((p7 ∧ False) → (p2 ∨ p4)) ∨ ((p5 ∨ p2) → (p5 → p5)))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p2 p1 : Prop)
theorem file86_41113 : (((((p0 → p0) → False) → ((p1 ∧ p2) → False)) → False) → False) := by
  intro assump_15
  have assump_39 : (((p0 → p0) → False) → ((p1 ∧ p2) → False)) := by
    intro assump_19
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      have assump_40 : (p0 → p0) := by
        intro assump_30
        exact assump_30
      let assump_29 := assump_19 assump_40
      apply False.elim assump_29
  let assump_18 := assump_15 assump_39
  apply False.elim assump_18


variable (p2 p7 p0 p5 p6 p1 p3 : Prop)
theorem file86_41662 : ((((((False ∨ p6) ∨ (True ∨ p5)) ∧ ((p2 → p7) → False)) → (((True ∨ p0) ∧ (p7 → p3)) ∧ ((p6 ∨ p1) ∨ (False → p0)))) → False) → False) := by
  intro assump_15
  have assump_119 : ((((False ∨ p6) ∨ (True ∨ p5)) ∧ ((p2 → p7) → False)) → (((True ∨ p0) ∧ (p7 → p3)) ∧ ((p6 ∨ p1) ∨ (False → p0)))) := by
    intro assump_19
    apply And.intro
    apply And.intro
    cases assump_19
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_22
        case inl assump_24 =>
          apply False.elim assump_24
        case inr assump_25 =>
          apply Or.inl
          apply True.intro
      case inr assump_23 =>
        cases assump_23
        case inl assump_32 =>
          apply Or.inl
          apply True.intro
        case inr assump_33 =>
          apply Or.inl
          apply True.intro
    intro assump_42
    cases assump_19
    case intro assump_45 assump_46 =>
      cases assump_45
      case inl assump_47 =>
        cases assump_47
        case inl assump_49 =>
          apply False.elim assump_49
        case inr assump_50 =>
          have assump_120 : (p2 → p7) := by
            intro assump_58
            exact assump_42
          let assump_57 := assump_46 assump_120
          apply False.elim assump_57
      case inr assump_48 =>
        cases assump_48
        case inl assump_64 =>
          have assump_121 : (p2 → p7) := by
            intro assump_71
            exact assump_42
          let assump_70 := assump_46 assump_121
          apply False.elim assump_70
        case inr assump_65 =>
          have assump_122 : (p2 → p7) := by
            intro assump_82
            exact assump_42
          let assump_81 := assump_46 assump_122
          apply False.elim assump_81
    cases assump_19
    case intro assump_88 assump_89 =>
      cases assump_88
      case inl assump_90 =>
        cases assump_90
        case inl assump_92 =>
          apply False.elim assump_92
        case inr assump_93 =>
          apply Or.inl
          apply Or.inl
          exact assump_93
      case inr assump_91 =>
        cases assump_91
        case inl assump_100 =>
          apply Or.inr
          intro assump_106
          apply False.elim assump_106
        case inr assump_101 =>
          apply Or.inr
          intro assump_113
          apply False.elim assump_113
  let assump_18 := assump_15 assump_119
  apply False.elim assump_18


variable (p1 p4 p0 p2 p3 p7 p5 : Prop)
theorem file86_44150 : (((((p2 ∨ p0) → False) ∧ ((p1 ∨ True) → False)) → (((p0 ∧ p7) ∨ (p7 → False)) ∧ ((p5 → p4) → (True → p5)))) ∧ ((((p3 ∧ p0) ∨ (p5 ∧ p4)) → False) → (((p7 ∧ p2) ∨ (p1 ∨ True)) → ((False ∧ p2) → False)))) := by
  apply And.intro
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_8
    have assump_39 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_3 assump_39
    apply False.elim assump_12
  intro assump_16
  intro assump_17
  cases assump_1
  case intro assump_22 assump_23 =>
    have assump_40 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_28 := assump_23 assump_40
    apply False.elim assump_28
  intro assump_32
  intro assump_33
  intro assump_34
  cases assump_34
  case intro assump_35 assump_36 =>
    apply False.elim assump_35


variable (p6 p3 p2 p5 : Prop)
theorem file86_45085 : (((((p6 → p5) ∨ (p3 ∧ p2)) → ((False ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : (((p6 → p5) ∨ (p3 ∧ p2)) → ((False ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p1 p7 p2 p0 p4 : Prop)
theorem file86_45511 : ((((((p3 → p4) ∧ (p2 → False)) → False) ∨ (((p7 → False) ∧ (p3 ∧ p0)) ∨ ((p1 → False) → False))) ∧ ((((p4 → False) ∨ (p7 ∨ p7)) → False) ∧ (((p7 → False) → (p7 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_82 : ((p7 → False) → (p7 → False)) := by
          intro assump_15
          intro assump_16
          have assump_83 : p7 := by
            exact assump_16
          let assump_21 := assump_15 assump_83
          apply False.elim assump_21
        let assump_14 := assump_9 assump_82
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_28 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            cases assump_3
            case intro assump_40 assump_41 =>
              have assump_84 : ((p7 → False) → (p7 → False)) := by
                intro assump_47
                intro assump_48
                have assump_85 : p7 := by
                  exact assump_48
                let assump_53 := assump_47 assump_85
                apply False.elim assump_53
              let assump_46 := assump_41 assump_84
              apply False.elim assump_46
      case inr assump_29 =>
        cases assump_3
        case intro assump_62 assump_63 =>
          have assump_86 : ((p7 → False) → (p7 → False)) := by
            intro assump_69
            intro assump_70
            have assump_87 : p7 := by
              exact assump_70
            let assump_75 := assump_69 assump_87
            apply False.elim assump_75
          let assump_68 := assump_63 assump_86
          apply False.elim assump_68


variable (p7 p6 p2 p5 p1 : Prop)
theorem file86_47405 : (((((p5 → False) → (p1 ∨ p2)) ∨ ((p6 → False) ∨ (p7 → p1))) ∧ (((True ∨ p6) → False) ∧ ((p6 ∧ False) ∨ (p2 → False)))) → False) := by
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_22
    case inl assump_24 =>
      cases assump_23
      case intro assump_28 assump_29 =>
        cases assump_29
        case inl assump_32 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            apply False.elim assump_35
        case inr assump_33 =>
          have assump_91 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_43 := assump_28 assump_91
          apply False.elim assump_43
    case inr assump_25 =>
      cases assump_25
      case inl assump_47 =>
        cases assump_23
        case intro assump_51 assump_52 =>
          cases assump_52
          case inl assump_55 =>
            cases assump_55
            case intro assump_57 assump_58 =>
              apply False.elim assump_58
          case inr assump_56 =>
            have assump_92 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_66 := assump_51 assump_92
            apply False.elim assump_66
      case inr assump_48 =>
        cases assump_23
        case intro assump_72 assump_73 =>
          cases assump_73
          case inl assump_76 =>
            cases assump_76
            case intro assump_78 assump_79 =>
              apply False.elim assump_79
          case inr assump_77 =>
            have assump_93 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_87 := assump_72 assump_93
            apply False.elim assump_87


variable (p2 p4 p5 p1 p7 p0 p3 p6 : Prop)
theorem file86_49193 : (((((p3 ∧ p4) ∨ (p7 ∧ p2)) → False) ∨ (((p0 → False) → False) → ((p0 ∧ p3) → (p5 ∨ False)))) → ((((p3 → False) → False) → ((False → False) → False)) → (((True → False) → False) → ((False ∧ p2) → (p1 ∨ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p5 p3 p6 p2 p1 p4 : Prop)
theorem file86_49617 : ((((((p2 ∧ p4) ∧ (p1 → False)) ∧ ((True → False) ∨ (p5 → p1))) → (((p2 ∧ p5) ∨ (False → p6)) ∨ ((p3 → False) → (True → p6)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p2 ∧ p4) ∧ (p1 → False)) ∧ ((True → False) ∨ (p5 → p1))) → (((p2 ∧ p5) ∨ (False → p6)) ∨ ((p3 → False) → (True → p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case inl assump_18 =>
            apply Or.inl
            apply Or.inr
            intro assump_22
            apply False.elim assump_22
          case inr assump_19 =>
            apply Or.inl
            apply Or.inr
            intro assump_27
            apply False.elim assump_27
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p4 p6 p0 p3 p1 : Prop)
theorem file86_50576 : ((((((p6 → p0) → (p1 ∨ True)) → ((p6 ∧ p6) → (True ∨ p3))) ∨ (((False → False) ∧ (p0 → p6)) ∨ ((p0 → False) ∧ (p3 → False)))) ∧ ((((p4 ∧ p4) ∧ (False ∧ True)) → ((False ∨ True) ∨ (p1 → False))) → False)) → False) := by
  intro assump_47
  cases assump_47
  case intro assump_48 assump_49 =>
    cases assump_48
    case inl assump_50 =>
      have assump_125 : (((p4 ∧ p4) ∧ (False ∧ True)) → ((False ∨ True) ∨ (p1 → False))) := by
        intro assump_57
        cases assump_57
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            cases assump_59
            case intro assump_66 assump_67 =>
              apply False.elim assump_66
      let assump_56 := assump_49 assump_125
      apply False.elim assump_56
    case inr assump_51 =>
      cases assump_51
      case inl assump_73 =>
        cases assump_73
        case intro assump_75 assump_76 =>
          have assump_126 : (((p4 ∧ p4) ∧ (False ∧ True)) → ((False ∨ True) ∨ (p1 → False))) := by
            intro assump_84
            cases assump_84
            case intro assump_85 assump_86 =>
              cases assump_85
              case intro assump_87 assump_88 =>
                cases assump_86
                case intro assump_93 assump_94 =>
                  apply False.elim assump_93
          let assump_83 := assump_49 assump_126
          apply False.elim assump_83
      case inr assump_74 =>
        cases assump_74
        case intro assump_100 assump_101 =>
          have assump_127 : (((p4 ∧ p4) ∧ (False ∧ True)) → ((False ∨ True) ∨ (p1 → False))) := by
            intro assump_109
            cases assump_109
            case intro assump_110 assump_111 =>
              cases assump_110
              case intro assump_112 assump_113 =>
                cases assump_111
                case intro assump_118 assump_119 =>
                  apply False.elim assump_118
          let assump_108 := assump_49 assump_127
          apply False.elim assump_108


variable (p2 p3 p6 p5 p1 p0 p4 : Prop)
theorem file86_52656 : ((((((p2 ∨ p0) → (p3 ∧ p6)) ∧ ((p6 ∧ p5) ∧ (False → p0))) → (((p4 ∨ p1) → False) → ((p4 ∨ p4) ∨ (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p2 ∨ p0) → (p3 ∧ p6)) ∧ ((p6 ∧ p5) ∧ (False → p0))) → (((p4 ∨ p1) → False) → ((p4 ∨ p4) ∨ (p4 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inr
          intro assump_23
          have assump_39 : (p4 ∨ p1) := by
            apply Or.inl
            exact assump_23
          let assump_31 := assump_6 assump_39
          apply False.elim assump_31
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p5 p7 p1 p6 : Prop)
theorem file86_53513 : ((((((True → p5) ∧ (True → False)) ∧ ((False → p7) ∨ (p6 → p1))) → False) → False) → False) := by
  intro assump_5
  have assump_37 : ((((True → p5) ∧ (True → False)) ∧ ((False → p7) ∨ (p6 → p1))) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case inl assump_18 =>
          have assump_38 : True := by
            apply True.intro
          let assump_23 := assump_13 assump_38
          apply False.elim assump_23
        case inr assump_19 =>
          have assump_39 : True := by
            apply True.intro
          let assump_30 := assump_13 assump_39
          apply False.elim assump_30
  let assump_8 := assump_5 assump_37
  apply False.elim assump_8


variable (p4 p5 p3 p6 p2 p7 p1 : Prop)
theorem file86_54377 : (((((p4 ∨ p1) ∨ (False ∨ True)) → False) → (((p1 ∨ p6) ∧ (p1 → False)) ∨ ((p6 → p5) ∧ (p5 ∨ False)))) ∧ ((((p3 → False) ∧ (False ∧ p4)) ∧ ((p1 ∧ p7) ∧ (p5 ∧ p3))) → (((p7 ∧ p1) ∨ (p1 → False)) ∨ ((p2 ∧ False) ∧ (False → False))))) := by
  apply And.intro
  intro assump_1
  have assump_27 : ((p4 ∨ p1) ∨ (False ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_12 := assump_1 assump_27
  apply False.elim assump_12
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply False.elim assump_23


variable (p3 p2 p4 p5 : Prop)
theorem file86_55106 : ((((((False ∧ True) → False) ∨ ((False ∨ p4) → (False → False))) ∨ (((p2 → p5) ∨ (p3 ∨ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ True) → False) ∨ ((False ∨ p4) → (False → False))) ∨ (((p2 → p5) ∨ (p3 ∨ p4)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p2 p3 p0 p5 p4 p1 p6 : Prop)
theorem file86_55642 : ((((((p4 → False) ∧ (p3 → p6)) → ((p1 ∧ p6) ∨ (p0 ∨ p3))) ∧ (((True → False) → (True ∨ p1)) → False)) ∧ ((((False ∨ p0) ∧ (p0 ∨ p5)) → ((p5 → p5) ∧ (p3 ∨ p0))) ∨ (((p3 ∧ p3) ∨ (p2 ∨ p0)) ∧ ((p6 ∧ False) ∨ (p0 ∨ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_133 : ((True → False) → (True ∨ p1)) := by
          intro assump_16
          apply Or.inl
          apply True.intro
        let assump_15 := assump_5 assump_133
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_22 assump_23 =>
          cases assump_22
          case inl assump_24 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              cases assump_23
              case inl assump_32 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  apply False.elim assump_35
              case inr assump_33 =>
                cases assump_33
                case inl assump_40 =>
                  have assump_134 : ((True → False) → (True ∨ p1)) := by
                    intro assump_48
                    apply Or.inl
                    apply True.intro
                  let assump_47 := assump_5 assump_134
                  apply False.elim assump_47
                case inr assump_41 =>
                  have assump_135 : ((True → False) → (True ∨ p1)) := by
                    intro assump_59
                    apply Or.inl
                    apply True.intro
                  let assump_58 := assump_5 assump_135
                  apply False.elim assump_58
          case inr assump_25 =>
            cases assump_25
            case inl assump_65 =>
              cases assump_23
              case inl assump_69 =>
                cases assump_69
                case intro assump_71 assump_72 =>
                  apply False.elim assump_72
              case inr assump_70 =>
                cases assump_70
                case inl assump_77 =>
                  have assump_136 : ((True → False) → (True ∨ p1)) := by
                    intro assump_84
                    apply Or.inl
                    apply True.intro
                  let assump_83 := assump_5 assump_136
                  apply False.elim assump_83
                case inr assump_78 =>
                  have assump_137 : ((True → False) → (True ∨ p1)) := by
                    intro assump_94
                    apply Or.inl
                    apply True.intro
                  let assump_93 := assump_5 assump_137
                  apply False.elim assump_93
            case inr assump_66 =>
              cases assump_23
              case inl assump_102 =>
                cases assump_102
                case intro assump_104 assump_105 =>
                  apply False.elim assump_105
              case inr assump_103 =>
                cases assump_103
                case inl assump_110 =>
                  have assump_138 : ((True → False) → (True ∨ p1)) := by
                    intro assump_117
                    apply Or.inl
                    apply True.intro
                  let assump_116 := assump_5 assump_138
                  apply False.elim assump_116
                case inr assump_111 =>
                  have assump_139 : ((True → False) → (True ∨ p1)) := by
                    intro assump_127
                    apply Or.inl
                    apply True.intro
                  let assump_126 := assump_5 assump_139
                  apply False.elim assump_126


variable (p5 p3 p1 p0 p4 p2 p6 : Prop)
theorem file86_59386 : (((((p3 → p3) ∨ (p0 → False)) ∧ ((p6 → False) → (True ∨ p5))) → False) → ((((p2 ∧ True) ∨ (p2 ∧ p6)) ∧ ((p0 → False) ∨ (p1 ∨ p4))) ∧ (((False → True) ∨ (True ∧ p2)) → ((True ∨ p4) ∧ (p4 ∨ False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_79 : (((p3 → p3) ∨ (p0 → False)) ∧ ((p6 → False) → (True ∨ p5))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    exact assump_5
    intro assump_8
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_79
  apply False.elim assump_4
  apply Or.inl
  intro assump_16
  have assump_80 : (((p3 → p3) ∨ (p0 → False)) ∧ ((p6 → False) → (True ∨ p5))) := by
    apply And.intro
    apply Or.inl
    intro assump_21
    exact assump_21
    intro assump_24
    apply Or.inl
    apply True.intro
  let assump_20 := assump_1 assump_80
  apply False.elim assump_20
  intro assump_30
  apply And.intro
  cases assump_30
  case inl assump_31 =>
    apply Or.inl
    apply True.intro
  case inr assump_32 =>
    cases assump_32
    case intro assump_37 assump_38 =>
      apply Or.inl
      apply True.intro
  cases assump_30
  case inl assump_45 =>
    have assump_81 : (((p3 → p3) ∨ (p0 → False)) ∧ ((p6 → False) → (True ∨ p5))) := by
      apply And.intro
      apply Or.inl
      intro assump_52
      exact assump_52
      intro assump_55
      apply Or.inl
      apply True.intro
    let assump_51 := assump_1 assump_81
    apply False.elim assump_51
  case inr assump_46 =>
    cases assump_46
    case intro assump_61 assump_62 =>
      have assump_82 : (((p3 → p3) ∨ (p0 → False)) ∧ ((p6 → False) → (True ∨ p5))) := by
        apply And.intro
        apply Or.inl
        intro assump_70
        exact assump_70
        intro assump_73
        apply Or.inl
        apply True.intro
      let assump_69 := assump_1 assump_82
      apply False.elim assump_69


variable (p5 p3 p0 p1 p4 p2 : Prop)
theorem file86_61304 : ((((((p5 ∧ False) → False) ∧ ((p1 ∧ p4) ∧ (p2 → False))) → (((p1 → False) ∨ (p4 ∧ p3)) ∨ ((p2 → False) → False))) ∧ ((((p3 → p3) ∧ (True ∨ p0)) ∨ ((p5 → False) ∨ (p0 → False))) → False)) → False) := by
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    have assump_37 : (((p3 → p3) ∧ (True ∨ p0)) ∨ ((p5 → False) ∨ (p0 → False))) := by
      apply Or.inl
      apply And.intro
      intro assump_31
      exact assump_31
      apply Or.inl
      apply True.intro
    let assump_30 := assump_25 assump_37
    apply False.elim assump_30


variable (p7 p5 p2 p6 : Prop)
theorem file86_61918 : ((((((False ∧ p2) ∧ (p5 → p5)) → False) ∨ (((False ∧ True) ∨ (p7 → False)) → False)) → ((((False ∧ p5) → False) ∨ ((p7 ∨ p7) → (p6 ∧ p5))) → False)) → False) := by
  intro assump_1
  have assump_21 : ((((False ∧ p2) ∧ (p5 → p5)) → False) ∨ (((False ∧ True) ∨ (p7 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_21
  have assump_22 : (((False ∧ p5) → False) ∨ ((p7 ∨ p7) → (p6 ∧ p5))) := by
    apply Or.inl
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
  let assump_12 := assump_4 assump_22
  apply False.elim assump_12


variable (p2 p0 p7 p1 p3 p4 p6 p5 : Prop)
theorem file86_62765 : ((((((p4 → True) ∧ (p2 ∧ p5)) ∧ ((True ∧ p4) ∨ (p6 → p6))) ∨ (((True ∧ p3) ∧ (True → False)) ∧ ((p3 ∧ p6) → (p4 ∧ p0)))) ∧ ((((False → p7) ∨ (False ∧ p1)) ∨ ((p7 ∧ p5) ∨ (p3 → p6))) → (((p3 ∧ p1) → (True ∧ True)) ∧ ((p1 → False) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_7
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_84 : (((False → p7) ∨ (False ∧ p1)) ∨ ((p7 ∧ p5) ∨ (p3 → p6))) := by
                  apply Or.inl
                  apply Or.inl
                  intro assump_29
                  apply False.elim assump_29
                let assump_28 := assump_3 assump_84
                let assump_32 := And.right assump_28
                let assump_34 := And.right assump_32
                have assump_85 : True := by
                  apply True.intro
                let assump_36 := assump_34 assump_85
                apply False.elim assump_36
            case inr assump_19 =>
              have assump_86 : (((False → p7) ∨ (False ∧ p1)) ∨ ((p7 ∧ p5) ∨ (p3 → p6))) := by
                apply Or.inl
                apply Or.inl
                intro assump_45
                apply False.elim assump_45
              let assump_44 := assump_3 assump_86
              let assump_48 := And.right assump_44
              let assump_50 := And.right assump_48
              have assump_87 : True := by
                apply True.intro
              let assump_52 := assump_50 assump_87
              apply False.elim assump_52
    case inr assump_5 =>
      cases assump_5
      case intro assump_56 assump_57 =>
        cases assump_56
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            have assump_88 : (((False → p7) ∨ (False ∧ p1)) ∨ ((p7 ∧ p5) ∨ (p3 → p6))) := by
              apply Or.inl
              apply Or.inl
              intro assump_73
              apply False.elim assump_73
            let assump_72 := assump_3 assump_88
            let assump_76 := And.right assump_72
            let assump_78 := And.right assump_76
            have assump_89 : True := by
              apply True.intro
            let assump_80 := assump_78 assump_89
            apply False.elim assump_80


variable (p7 p4 p2 p0 p1 : Prop)
theorem file86_65426 : (((((p4 ∧ False) ∧ (True ∧ p7)) → False) → False) → ((((p4 ∨ p1) ∧ (p0 ∧ p4)) ∧ ((p4 → False) ∧ (p1 → True))) → (((p1 ∧ p2) → False) → ((True → False) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_2
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_15
        case intro assump_20 assump_21 =>
          cases assump_13
          case intro assump_26 assump_27 =>
            have assump_76 : (((p4 ∧ False) ∧ (True ∧ p7)) → False) := by
              intro assump_35
              cases assump_35
              case intro assump_36 assump_37 =>
                cases assump_36
                case intro assump_38 assump_39 =>
                  apply False.elim assump_39
            let assump_34 := assump_1 assump_76
            apply False.elim assump_34
      case inr assump_17 =>
        cases assump_15
        case intro assump_49 assump_50 =>
          cases assump_13
          case intro assump_55 assump_56 =>
            have assump_77 : (((p4 ∧ False) ∧ (True ∧ p7)) → False) := by
              intro assump_64
              cases assump_64
              case intro assump_65 assump_66 =>
                cases assump_65
                case intro assump_67 assump_68 =>
                  apply False.elim assump_68
            let assump_63 := assump_1 assump_77
            apply False.elim assump_63


variable (p0 p1 p3 p4 p5 : Prop)
theorem file86_66997 : (((((p0 → p0) ∨ (p4 ∨ True)) → False) → False) ∨ ((((p4 ∨ True) ∧ (p1 ∨ p3)) ∨ ((p0 → p0) ∧ (p5 ∨ p0))) → (((p4 → True) ∨ (p3 ∨ p0)) ∧ ((False → False) → (p4 ∧ p1))))) := by
  apply Or.inl
  intro assump_5
  have assump_15 : ((p0 → p0) ∨ (p4 ∨ True)) := by
    apply Or.inl
    intro assump_9
    exact assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p6 p5 p7 p0 p2 : Prop)
theorem file86_67431 : ((((((p5 → p0) → (False ∨ p6)) ∧ ((False → False) → (p6 ∨ p5))) → (((False ∨ p5) → (p5 ∨ p6)) ∨ ((p6 → False) ∧ (p2 → p7)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 → p0) → (False ∨ p6)) ∧ ((False → False) → (p6 ∨ p5))) → (((False ∨ p5) → (p5 ∨ p6)) ∨ ((p6 → False) ∧ (p2 → p7)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        apply False.elim assump_13
      case inr assump_14 =>
        apply Or.inl
        exact assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p1 p6 p2 p7 : Prop)
theorem file86_68137 : ((((((p1 ∨ p6) → (True ∨ p1)) → False) → (((p6 → False) → False) → ((p2 → p7) ∨ (False → True)))) → False) → False) := by
  intro assump_11
  have assump_39 : ((((p1 ∨ p6) → (True ∨ p1)) → False) → (((p6 → False) → False) → ((p2 → p7) ∨ (False → True)))) := by
    intro assump_15
    intro assump_16
    apply Or.inl
    intro assump_21
    have assump_40 : ((p1 ∨ p6) → (True ∨ p1)) := by
      intro assump_26
      cases assump_26
      case inl assump_27 =>
        apply Or.inl
        apply True.intro
      case inr assump_28 =>
        apply Or.inl
        apply True.intro
    let assump_25 := assump_15 assump_40
    apply False.elim assump_25
  let assump_14 := assump_11 assump_39
  apply False.elim assump_14


variable (p1 p5 p7 p4 p6 p0 : Prop)
theorem file86_68920 : (((((p1 ∧ True) ∨ (p1 ∧ p1)) ∧ ((True → False) → (p4 ∧ p6))) ∧ (((p1 → False) ∨ (p1 ∨ p4)) → ((p4 ∧ True) ∧ (p4 → False)))) ∨ ((((p4 → False) ∧ (p4 ∧ p5)) → ((p5 → p7) ∧ (p5 → False))) ∨ (((False → False) → False) ∨ ((p0 → False) → False)))) := by
  apply Or.inr
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_40 : p4 := by
        exact assump_9
      let assump_17 := assump_5 assump_40
      apply False.elim assump_17
  intro assump_21
  cases assump_1
  case intro assump_24 assump_25 =>
    cases assump_25
    case intro assump_28 assump_29 =>
      have assump_41 : p4 := by
        exact assump_28
      let assump_36 := assump_24 assump_41
      apply False.elim assump_36


variable (p5 p7 p0 p6 p4 p3 p1 : Prop)
theorem file86_69811 : ((((((p1 ∧ p4) → False) → ((p7 → p5) ∧ (p3 → False))) → False) ∧ ((((p6 ∧ p5) ∧ (p6 ∧ p7)) → ((p4 → p0) ∧ (p1 → p3))) ∧ (((True → False) ∧ (p5 ∧ p6)) ∧ ((p0 ∧ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            have assump_31 : True := by
              apply True.intro
            let assump_27 := assump_12 assump_31
            apply False.elim assump_27


variable (p4 p1 p7 p6 : Prop)
theorem file86_70534 : (((((p7 → True) → (p7 ∧ False)) → ((p4 ∧ p4) ∧ (p1 ∧ p7))) → (((p1 ∨ p7) ∨ (p1 → p1)) → False)) → ((((False → False) ∧ (False → False)) → False) → (((True → True) → False) → ((True → p6) ∧ (p1 → False))))) := by
  intro assump_15
  intro assump_16
  intro assump_17
  apply And.intro
  intro assump_18
  have assump_110 : (((p7 → True) → (p7 ∧ False)) → ((p4 ∧ p4) ∧ (p1 ∧ p7))) := by
    intro assump_28
    apply And.intro
    apply And.intro
    have assump_111 : (p7 → True) := by
      intro assump_32
      apply True.intro
    let assump_31 := assump_28 assump_111
    let assump_33 := And.right assump_31
    apply False.elim assump_33
    have assump_112 : (p7 → True) := by
      intro assump_41
      apply True.intro
    let assump_40 := assump_28 assump_112
    let assump_42 := And.right assump_40
    apply False.elim assump_42
    apply And.intro
    have assump_113 : (p7 → True) := by
      intro assump_50
      apply True.intro
    let assump_49 := assump_28 assump_113
    let assump_51 := And.right assump_49
    apply False.elim assump_51
    have assump_114 : (p7 → True) := by
      intro assump_59
      apply True.intro
    let assump_58 := assump_28 assump_114
    let assump_60 := And.left assump_58
    exact assump_60
  let assump_27 := assump_15 assump_110
  have assump_115 : ((p1 ∨ p7) ∨ (p1 → p1)) := by
    apply Or.inr
    intro assump_63
    exact assump_63
  let assump_62 := assump_27 assump_115
  apply False.elim assump_62
  intro assump_69
  have assump_116 : (((p7 → True) → (p7 ∧ False)) → ((p4 ∧ p4) ∧ (p1 ∧ p7))) := by
    intro assump_79
    apply And.intro
    apply And.intro
    have assump_117 : (p7 → True) := by
      intro assump_83
      apply True.intro
    let assump_82 := assump_79 assump_117
    let assump_84 := And.right assump_82
    apply False.elim assump_84
    have assump_118 : (p7 → True) := by
      intro assump_92
      apply True.intro
    let assump_91 := assump_79 assump_118
    let assump_93 := And.right assump_91
    apply False.elim assump_93
    apply And.intro
    exact assump_69
    have assump_119 : (p7 → True) := by
      intro assump_103
      apply True.intro
    let assump_102 := assump_79 assump_119
    let assump_104 := And.left assump_102
    exact assump_104
  let assump_78 := assump_15 assump_116
  have assump_120 : ((p1 ∨ p7) ∨ (p1 → p1)) := by
    apply Or.inl
    apply Or.inl
    exact assump_69
  let assump_106 := assump_78 assump_120
  apply False.elim assump_106


variable (p6 p2 p5 p0 p4 p7 p1 p3 : Prop)
theorem file86_73071 : (((((p0 → p3) ∧ (p6 → False)) → ((p0 ∨ p3) → False)) → (((p4 ∨ p5) ∨ (p5 ∨ p3)) ∧ ((p3 ∧ p0) ∧ (p7 → p6)))) → ((((p2 → p0) → False) → False) → (((p2 → p2) ∨ (p2 → p3)) ∨ ((p1 ∨ p2) → (p2 → p0))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  intro assump_7
  exact assump_7


variable (p1 p6 p5 : Prop)
theorem file86_73423 : ((((((p1 ∧ p6) ∧ (p1 ∧ False)) ∨ ((p6 ∨ p5) ∧ (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_45 : ((((p1 ∧ p6) ∧ (p1 ∧ False)) ∨ ((p6 ∨ p5) ∧ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
    case inr assump_7 =>
      cases assump_7
      case intro assump_22 assump_23 =>
        cases assump_22
        case inl assump_24 =>
          have assump_46 : True := by
            apply True.intro
          let assump_30 := assump_23 assump_46
          apply False.elim assump_30
        case inr assump_25 =>
          have assump_47 : True := by
            apply True.intro
          let assump_38 := assump_23 assump_47
          apply False.elim assump_38
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p4 p2 p5 p3 p1 p0 p6 : Prop)
theorem file86_74526 : (((((p1 → p2) → False) ∧ ((False → False) → False)) → False) ∨ ((((p1 ∨ True) → False) ∧ ((True ∧ p5) ∧ (p0 → p5))) ∨ (((False ∧ p6) → (p3 ∨ p6)) → ((p0 ∨ p3) ∨ (p4 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p2 p5 p0 p4 p1 p3 p6 : Prop)
theorem file86_75020 : ((((((p0 → p6) ∨ (p5 ∨ p2)) → ((p2 → True) ∨ (p3 ∨ p1))) ∨ (((False → False) ∧ (p3 → p0)) ∧ ((p4 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p0 → p6) ∨ (p5 ∨ p2)) → ((p2 → True) ∨ (p3 ∨ p1))) ∨ (((False → False) ∧ (p3 → p0)) ∧ ((p4 → False) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_11 =>
        apply Or.inl
        intro assump_15
        apply True.intro
      case inr assump_12 =>
        apply Or.inl
        intro assump_18
        apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p5 p6 p2 p1 p3 p4 p0 : Prop)
theorem file86_75835 : (((((False ∧ True) ∨ (p0 ∨ p2)) ∧ ((p5 → False) → (True ∧ p6))) → (((p4 ∨ p7) ∨ (p0 → p3)) ∨ ((p0 → p4) ∨ (p2 ∨ p7)))) → ((((p1 ∧ p1) → (True ∨ p3)) → ((True → False) → (p5 → p5))) ∨ (((False → False) ∨ (p5 → False)) → False))) := by
  intro assump_7
  apply Or.inl
  intro assump_10
  intro assump_11
  intro assump_12
  exact assump_12


variable (p6 p3 p0 p2 p5 : Prop)
theorem file86_76230 : ((((((p3 ∧ p0) → False) ∨ ((p2 → False) ∨ (p0 ∨ p6))) → False) ∧ ((((p3 ∨ p3) ∧ (True ∧ False)) ∨ ((p2 ∧ p5) → (p3 ∧ p2))) ∧ (((p5 → p5) ∨ (False → p3)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_15
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
          case inr assump_17 =>
            cases assump_15
            case intro assump_28 assump_29 =>
              apply False.elim assump_29
      case inr assump_13 =>
        have assump_45 : ((p5 → p5) ∨ (False → p3)) := by
          apply Or.inl
          intro assump_39
          exact assump_39
        let assump_38 := assump_11 assump_45
        apply False.elim assump_38


variable (p7 p3 p1 p0 p5 p2 : Prop)
theorem file86_77271 : (((((p3 → False) → False) → ((p5 → False) ∨ (p2 ∧ p7))) → False) → ((((p1 → p5) ∨ (p3 ∨ p0)) → ((p3 ∧ False) → False)) ∨ (((p5 ∨ p2) → False) ∨ ((False ∧ p0) → (p5 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p2 p4 p1 p5 p7 : Prop)
theorem file86_77655 : ((((((p4 → False) → False) → False) ∧ (((p2 → False) → (p1 ∨ p1)) ∧ ((True → False) ∧ (p7 ∨ p5)))) ∨ ((((p1 → p7) → (p7 ∧ p4)) ∨ ((p7 → False) ∧ (p2 ∨ p1))) ∧ (((p7 → False) ∧ (False ∧ p7)) ∧ ((False ∧ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            have assump_78 : True := by
              apply True.intro
            let assump_21 := assump_12 assump_78
            apply False.elim assump_21
          case inr assump_17 =>
            have assump_79 : True := by
              apply True.intro
            let assump_28 := assump_12 assump_79
            apply False.elim assump_28
  case inr assump_3 =>
    cases assump_3
    case intro assump_32 assump_33 =>
      cases assump_32
      case inl assump_34 =>
        cases assump_33
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            cases assump_41
            case intro assump_44 assump_45 =>
              apply False.elim assump_44
      case inr assump_35 =>
        cases assump_35
        case intro assump_48 assump_49 =>
          cases assump_49
          case inl assump_52 =>
            cases assump_33
            case intro assump_56 assump_57 =>
              cases assump_56
              case intro assump_58 assump_59 =>
                cases assump_59
                case intro assump_62 assump_63 =>
                  apply False.elim assump_62
          case inr assump_53 =>
            cases assump_33
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                cases assump_71
                case intro assump_74 assump_75 =>
                  apply False.elim assump_74


variable (p1 p6 p0 p4 p3 p5 p2 : Prop)
theorem file86_79718 : ((((((p4 ∨ p3) → (p0 ∨ True)) ∨ ((p5 → p2) → (p6 → p0))) ∨ (((p1 ∨ p5) ∧ (p5 → False)) ∨ ((p2 → p5) → False))) → False) → False) := by
  intro assump_5
  have assump_19 : ((((p4 ∨ p3) → (p0 ∨ True)) ∨ ((p5 → p2) → (p6 → p0))) ∨ (((p1 ∨ p5) ∧ (p5 → False)) ∨ ((p2 → p5) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply Or.inr
      apply True.intro
    case inr assump_11 =>
      apply Or.inr
      apply True.intro
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p2 p5 p1 p3 p0 p4 p7 : Prop)
theorem file86_80340 : ((((((p7 → True) ∧ (True ∧ p0)) ∧ ((p5 ∨ p2) ∧ (False ∧ p3))) ∧ (((True ∧ p7) → (True → True)) → False)) ∨ ((((p1 ∧ p5) → (False → False)) ∨ ((p4 → False) → (p7 → False))) → False)) → False) := by
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_22
          case intro assump_25 assump_26 =>
            cases assump_20
            case intro assump_31 assump_32 =>
              cases assump_31
              case inl assump_33 =>
                cases assump_32
                case intro assump_37 assump_38 =>
                  apply False.elim assump_37
              case inr assump_34 =>
                cases assump_32
                case intro assump_43 assump_44 =>
                  apply False.elim assump_43
  case inr assump_16 =>
    have assump_57 : (((p1 ∧ p5) → (False → False)) ∨ ((p4 → False) → (p7 → False))) := by
      apply Or.inl
      intro assump_50
      intro assump_51
      apply False.elim assump_51
    let assump_49 := assump_16 assump_57
    apply False.elim assump_49


variable (p0 p3 p4 p1 p5 p6 p2 p7 : Prop)
theorem file86_81632 : (((((p3 → False) → False) ∨ ((False ∧ p7) → (p5 → p6))) → False) → ((((p0 → False) ∧ (p0 ∧ p3)) ∧ ((p1 → p0) ∧ (p5 → p3))) → (((p3 → p5) → (p2 ∨ p5)) → ((False → p4) → (p3 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_2
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        cases assump_13
        case intro assump_24 assump_25 =>
          have assump_43 : (((p3 → False) → False) ∨ ((False ∧ p7) → (p5 → p6))) := by
            apply Or.inl
            intro assump_33
            have assump_44 : p3 := by
              exact assump_19
            let assump_36 := assump_33 assump_44
            apply False.elim assump_36
          let assump_32 := assump_1 assump_43
          apply False.elim assump_32


variable (p1 p3 p0 p7 p2 : Prop)
theorem file86_82583 : ((((((p7 → False) → (p0 → False)) → ((False → p0) ∨ (p7 → False))) → False) ∧ ((((p3 ∨ p0) ∧ (True → p3)) → ((True → False) → False)) ∧ (((p7 → p7) → False) ∧ ((False → p2) ∨ (True ∧ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          have assump_40 : (p7 → p7) := by
            intro assump_20
            exact assump_20
          let assump_19 := assump_10 assump_40
          apply False.elim assump_19
        case inr assump_15 =>
          cases assump_15
          case intro assump_26 assump_27 =>
            have assump_41 : (p7 → p7) := by
              intro assump_34
              exact assump_34
            let assump_33 := assump_10 assump_41
            apply False.elim assump_33


variable (p0 p1 p7 p4 p2 p6 : Prop)
theorem file86_83563 : (((((p4 ∧ False) → False) → ((False → True) ∨ (p7 ∨ False))) ∧ (((p0 → False) → (False → False)) → False)) → ((((True → p2) → False) ∧ ((p6 → False) → False)) ∧ (((p7 ∨ p2) → (p1 ∧ p0)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_53 : ((p0 → False) → (False → False)) := by
      intro assump_12
      intro assump_13
      apply False.elim assump_13
    let assump_11 := assump_6 assump_53
    apply False.elim assump_11
  intro assump_19
  cases assump_1
  case intro assump_22 assump_23 =>
    have assump_54 : ((p0 → False) → (False → False)) := by
      intro assump_29
      intro assump_30
      apply False.elim assump_30
    let assump_28 := assump_23 assump_54
    apply False.elim assump_28
  intro assump_36
  cases assump_1
  case intro assump_39 assump_40 =>
    have assump_55 : ((p0 → False) → (False → False)) := by
      intro assump_46
      intro assump_47
      apply False.elim assump_47
    let assump_45 := assump_40 assump_55
    apply False.elim assump_45


variable (p2 p1 p3 p6 : Prop)
theorem file86_84709 : (((((p6 → False) → False) ∧ ((p2 ∧ p6) ∧ (True → False))) → False) ∧ ((((p6 → False) → (False → p3)) → False) → (((True → False) → (p3 → False)) ∧ ((p2 → p1) ∨ (p2 ∧ False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_51 : True := by
          apply True.intro
        let assump_16 := assump_7 assump_51
        apply False.elim assump_16
  intro assump_20
  apply And.intro
  intro assump_21
  intro assump_22
  have assump_52 : ((p6 → False) → (False → p3)) := by
    intro assump_30
    intro assump_31
    apply False.elim assump_31
  let assump_29 := assump_20 assump_52
  apply False.elim assump_29
  apply Or.inl
  intro assump_39
  have assump_53 : ((p6 → False) → (False → p3)) := by
    intro assump_44
    intro assump_45
    apply False.elim assump_45
  let assump_43 := assump_20 assump_53
  apply False.elim assump_43


variable (p0 p5 p6 p7 p2 p4 : Prop)
theorem file86_85787 : ((((((p0 ∨ True) ∧ (p4 → False)) ∧ ((p4 ∨ p2) → (p5 ∧ False))) → (((True ∨ p7) ∨ (p2 ∧ False)) ∨ ((p7 ∧ p6) ∨ (p5 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p0 ∨ True) ∧ (p4 → False)) ∧ ((p4 ∨ p2) → (p5 ∧ False))) → (((True ∨ p7) ∨ (p2 ∧ False)) ∨ ((p7 ∧ p6) ∨ (p5 ∧ p4)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_11 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p6 p0 p5 p4 p7 p2 p1 p3 : Prop)
theorem file86_86636 : (((((p6 ∨ p6) ∨ (p1 ∧ p4)) ∨ ((p1 → False) ∨ (p6 → p1))) → False) → ((((p5 → p0) → (p6 → p3)) → ((p4 → False) ∧ (p7 ∨ p3))) → (((p4 ∧ False) ∧ (p3 ∨ False)) → ((p2 → p1) → (p6 ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      apply False.elim assump_10


variable (p7 p4 p6 p2 p1 p3 p5 p0 : Prop)
theorem file86_87104 : (((((p2 ∧ p5) ∧ (p3 ∧ p1)) → ((p3 → False) ∨ (p2 ∧ p1))) ∧ (((p1 → True) → False) ∧ ((p0 → p0) ∧ (p0 ∧ p7)))) → ((((True → False) ∨ (p7 ∧ True)) ∨ ((p0 ∧ p4) ∧ (p2 ∧ p6))) ∧ (((p3 → False) → False) → ((True ∨ p7) ∨ (p5 → p2))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply Or.inl
          apply Or.inl
          intro assump_20
          have assump_53 : (p1 → True) := by
            intro assump_28
            apply True.intro
          let assump_27 := assump_6 assump_53
          apply False.elim assump_27
  intro assump_32
  cases assump_1
  case intro assump_35 assump_36 =>
    cases assump_36
    case intro assump_39 assump_40 =>
      cases assump_40
      case intro assump_43 assump_44 =>
        cases assump_44
        case intro assump_47 assump_48 =>
          apply Or.inl
          apply Or.inl
          apply True.intro


variable (p2 p3 p6 p1 p0 p4 : Prop)
theorem file86_88254 : ((((((False → p0) → (p6 → p4)) → ((p2 → p2) ∨ (p1 ∧ True))) ∨ (((p3 → True) → False) ∧ ((True ∧ p3) → (p0 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((False → p0) → (p6 → p4)) → ((p2 → p2) ∨ (p1 ∧ True))) ∨ (((p3 → True) → False) ∧ ((True ∧ p3) → (p0 ∧ p2)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p6 p7 p1 p3 p4 p5 : Prop)
theorem file86_88767 : (((((False ∧ p3) ∧ (p5 → False)) ∧ ((False → p7) → (False → False))) ∧ (((p6 ∨ p7) ∨ (p4 → False)) ∨ ((p5 ∧ p4) → False))) → ((((False ∨ p7) ∧ (p1 → False)) → False) ∨ (((p5 → False) → False) → ((p7 → False) ∨ (p2 → False))))) := by
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


variable (p6 p5 p1 p0 p4 : Prop)
theorem file86_89338 : ((((((p6 ∨ p4) → (True ∨ p0)) ∨ ((p0 → p5) ∨ (p0 → False))) ∨ (((p5 ∧ p5) → (False → False)) ∧ ((p4 ∨ p1) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 ∨ p4) → (True ∨ p0)) ∨ ((p0 → p5) ∨ (p0 → False))) ∨ (((p5 ∧ p5) → (False → False)) ∧ ((p4 ∨ p1) ∧ (p5 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p1 p0 p5 p3 p6 p7 : Prop)
theorem file86_89984 : (((((p4 → True) ∧ (p4 → True)) → False) ∧ (((p6 ∨ p7) ∧ (p3 ∨ p5)) → ((p0 → p4) → (p4 → p1)))) → ((((p4 → p7) ∧ (p3 → False)) ∧ ((p7 ∨ True) ∨ (p5 ∨ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_1
          case intro assump_17 assump_18 =>
            have assump_77 : ((p4 → True) ∧ (p4 → True)) := by
              apply And.intro
              intro assump_25
              apply True.intro
              intro assump_26
              apply True.intro
            let assump_24 := assump_17 assump_77
            apply False.elim assump_24
        case inr assump_14 =>
          cases assump_1
          case intro assump_32 assump_33 =>
            have assump_78 : ((p4 → True) ∧ (p4 → True)) := by
              apply And.intro
              intro assump_40
              apply True.intro
              intro assump_41
              apply True.intro
            let assump_39 := assump_32 assump_78
            apply False.elim assump_39
      case inr assump_12 =>
        cases assump_12
        case inl assump_45 =>
          cases assump_1
          case intro assump_49 assump_50 =>
            have assump_79 : ((p4 → True) ∧ (p4 → True)) := by
              apply And.intro
              intro assump_57
              apply True.intro
              intro assump_58
              apply True.intro
            let assump_56 := assump_49 assump_79
            apply False.elim assump_56
        case inr assump_46 =>
          cases assump_1
          case intro assump_64 assump_65 =>
            have assump_80 : ((p4 → True) ∧ (p4 → True)) := by
              apply And.intro
              intro assump_72
              apply True.intro
              intro assump_73
              apply True.intro
            let assump_71 := assump_64 assump_80
            apply False.elim assump_71


variable (p7 p1 p4 p0 p2 p5 p3 p6 : Prop)
theorem file86_92094 : (((((p1 ∨ True) ∧ (p7 → False)) ∨ ((p2 ∧ p7) → False)) ∧ (((p3 ∧ p7) ∧ (p1 → False)) ∧ ((p4 → False) → False))) → ((((True ∨ p7) ∨ (True ∨ True)) ∨ ((p0 → False) → False)) ∨ (((p7 ∨ p0) ∧ (p6 ∨ False)) ∧ ((p7 → p5) → (p6 → p6))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
        case inr assump_13 =>
          cases assump_7
          case intro assump_36 assump_37 =>
            cases assump_36
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
    case inr assump_9 =>
      cases assump_7
      case intro assump_52 assump_53 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro


variable (p5 p0 p3 p4 p6 p1 p7 : Prop)
theorem file86_93742 : (((((p0 ∨ True) ∧ (p7 ∨ True)) → ((False ∧ False) ∧ (p4 ∨ p3))) → False) ∨ ((((p1 ∧ p5) ∨ (p7 ∧ p7)) ∧ ((False → False) ∨ (True → False))) → (((p3 → p4) ∨ (p7 → True)) ∧ ((False ∨ p6) ∨ (p5 ∧ p6))))) := by
  apply Or.inl
  intro assump_1
  have assump_10 : ((p0 ∨ True) ∧ (p7 ∨ True)) := by
    apply And.intro
    apply Or.inr
    apply True.intro
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_10
  let assump_5 := And.left assump_4
  let assump_6 := And.left assump_5
  apply False.elim assump_6


variable (p3 p0 p6 p4 p1 : Prop)
theorem file86_94323 : (((((p3 ∧ p4) → (p1 → True)) → ((p4 ∨ p0) → False)) ∧ (((p6 ∧ p1) → (p0 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p6 ∧ p1) → (p0 ∨ True)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p0 p1 p5 p4 : Prop)
theorem file86_94804 : ((((((p4 ∨ p6) ∨ (p0 ∧ p6)) → False) → (((p1 ∧ p5) → (p6 → p6)) → ((p6 → False) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p4 ∨ p6) ∨ (p0 ∧ p6)) → False) → (((p1 ∧ p5) → (p6 → p6)) → ((p6 → False) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    intro assump_11
    have assump_23 : ((p4 ∨ p6) ∨ (p0 ∧ p6)) := by
      apply Or.inl
      apply Or.inr
      exact assump_11
    let assump_15 := assump_5 assump_23
    apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p3 p1 p6 p0 p7 p5 : Prop)
theorem file86_95449 : (((((p4 → p3) ∧ (False → p1)) → False) → (((p0 ∧ p6) ∧ (p0 ∧ p3)) → False)) ∨ ((((p5 → False) ∧ (p7 ∧ p7)) → ((p0 → False) → False)) ∨ (((True → False) → False) → ((p6 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        have assump_29 : ((p4 → p3) ∧ (False → p1)) := by
          apply And.intro
          intro assump_20
          exact assump_12
          intro assump_23
          apply False.elim assump_23
        let assump_19 := assump_1 assump_29
        apply False.elim assump_19


variable (p7 p2 p6 p5 p3 : Prop)
theorem file86_96192 : (((((p6 → p7) → (p2 → False)) → False) → False) → ((((p5 ∨ True) ∨ (p2 ∨ True)) → ((True → False) → False)) ∨ (((p7 ∨ p2) → False) → ((p5 → False) → (False → p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_8
    case inl assump_10 =>
      have assump_40 : True := by
        apply True.intro
      let assump_15 := assump_5 assump_40
      apply False.elim assump_15
    case inr assump_11 =>
      have assump_41 : True := by
        apply True.intro
      let assump_21 := assump_5 assump_41
      apply False.elim assump_21
  case inr assump_9 =>
    cases assump_9
    case inl assump_25 =>
      have assump_42 : True := by
        apply True.intro
      let assump_30 := assump_5 assump_42
      apply False.elim assump_30
    case inr assump_26 =>
      have assump_43 : True := by
        apply True.intro
      let assump_36 := assump_5 assump_43
      apply False.elim assump_36


variable (p6 p1 p5 p7 p0 p4 p2 p3 : Prop)
theorem file86_97237 : (((((False → False) ∧ (p0 ∨ p4)) ∨ ((p5 ∨ p7) → (p0 → p4))) ∧ (((p7 ∨ p3) → False) ∨ ((p4 → p0) → (False → p1)))) → ((((p7 ∧ p6) → (p5 → False)) → ((False ∧ p5) → (p1 ∨ p6))) ∨ (((False → p6) ∨ (True ∨ False)) ∨ ((p2 ∨ p0) → (p5 ∨ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_3
          case inl assump_14 =>
            apply Or.inl
            intro assump_18
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              apply False.elim assump_20
          case inr assump_15 =>
            apply Or.inl
            intro assump_26
            intro assump_27
            cases assump_27
            case intro assump_28 assump_29 =>
              apply False.elim assump_28
        case inr assump_11 =>
          cases assump_3
          case inl assump_34 =>
            apply Or.inl
            intro assump_38
            intro assump_39
            cases assump_39
            case intro assump_40 assump_41 =>
              apply False.elim assump_40
          case inr assump_35 =>
            apply Or.inl
            intro assump_46
            intro assump_47
            cases assump_47
            case intro assump_48 assump_49 =>
              apply False.elim assump_48
    case inr assump_5 =>
      cases assump_3
      case inl assump_54 =>
        apply Or.inl
        intro assump_58
        intro assump_59
        cases assump_59
        case intro assump_60 assump_61 =>
          apply False.elim assump_60
      case inr assump_55 =>
        apply Or.inl
        intro assump_66
        intro assump_67
        cases assump_67
        case intro assump_68 assump_69 =>
          apply False.elim assump_68


variable (p2 p0 p5 p3 p6 p7 p4 : Prop)
theorem file86_99207 : (((((p7 → p4) → (p7 → p3)) → ((False ∧ p4) → (p7 → p6))) ∧ (((False ∧ False) → False) ∨ ((p6 → False) ∨ (False ∨ p2)))) ∨ ((((p7 → p7) ∨ (True ∨ p2)) → False) ∧ (((p7 ∧ p3) ∧ (p2 → False)) ∧ ((p0 → p5) → False)))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_6
  apply Or.inl
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    apply False.elim assump_11


variable (p6 p1 : Prop)
theorem file86_99758 : (((((p6 ∨ False) ∨ (p1 → p1)) ∧ ((False → False) ∨ (True ∧ True))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p6 ∨ False) ∨ (p1 → p1)) ∧ ((False → False) ∨ (True ∧ True))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    exact assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p4 p7 p1 p2 p5 p0 : Prop)
theorem file86_100225 : (((((True ∧ p2) → (False → p4)) ∨ ((True ∧ p6) → (p1 ∧ p6))) → False) → ((((p7 → False) → (p5 ∨ p0)) → False) ∧ (((p0 → False) ∨ (p2 → p4)) ∧ ((True → False) ∧ (p1 ∧ p5))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_62 : (((True ∧ p2) → (False → p4)) ∨ ((True ∧ p6) → (p1 ∧ p6))) := by
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_62
  apply False.elim assump_7
  apply And.intro
  apply Or.inl
  intro assump_17
  have assump_63 : (((True ∧ p2) → (False → p4)) ∨ ((True ∧ p6) → (p1 ∧ p6))) := by
    apply Or.inl
    intro assump_22
    intro assump_23
    apply False.elim assump_23
  let assump_21 := assump_1 assump_63
  apply False.elim assump_21
  apply And.intro
  intro assump_29
  have assump_64 : (((True ∧ p2) → (False → p4)) ∨ ((True ∧ p6) → (p1 ∧ p6))) := by
    apply Or.inl
    intro assump_35
    intro assump_36
    apply False.elim assump_36
  let assump_34 := assump_1 assump_64
  apply False.elim assump_34
  apply And.intro
  have assump_65 : (((True ∧ p2) → (False → p4)) ∨ ((True ∧ p6) → (p1 ∧ p6))) := by
    apply Or.inl
    intro assump_45
    intro assump_46
    apply False.elim assump_46
  let assump_44 := assump_1 assump_65
  apply False.elim assump_44
  have assump_66 : (((True ∧ p2) → (False → p4)) ∨ ((True ∧ p6) → (p1 ∧ p6))) := by
    apply Or.inl
    intro assump_55
    intro assump_56
    apply False.elim assump_56
  let assump_54 := assump_1 assump_66
  apply False.elim assump_54


variable (p5 p3 : Prop)
theorem file86_101800 : ((((((True ∨ p3) → False) ∧ ((p3 ∨ True) ∨ (False ∧ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_34 : ((((True ∨ p3) → False) ∧ ((p3 ∨ True) ∨ (False ∧ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_35 : (True ∨ p3) := by
            apply Or.inl
            apply True.intro
          let assump_17 := assump_6 assump_35
          apply False.elim assump_17
        case inr assump_13 =>
          have assump_36 : (True ∨ p3) := by
            apply Or.inl
            apply True.intro
          let assump_23 := assump_6 assump_36
          apply False.elim assump_23
      case inr assump_11 =>
        cases assump_11
        case intro assump_27 assump_28 =>
          apply False.elim assump_27
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p2 p6 p5 p3 p7 p4 p0 : Prop)
theorem file86_102828 : ((((((p5 ∨ True) ∨ (True → p4)) ∨ ((p3 ∨ p2) ∧ (p0 ∨ False))) ∨ (((False → p7) → (p0 → False)) ∧ ((p2 ∧ False) → (p7 → p6)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p5 ∨ True) ∨ (True → p4)) ∨ ((p3 ∨ p2) ∧ (p0 ∨ False))) ∨ (((False → p7) → (p0 → False)) ∧ ((p2 ∧ False) → (p7 → p6)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p6 p4 p2 p7 p5 : Prop)
theorem file86_103356 : (((((p5 ∧ p1) ∨ (p4 → False)) ∧ ((True ∨ p4) ∧ (p1 → False))) → False) → ((((p7 ∨ p2) → False) → False) → (((False ∧ p4) → False) ∨ ((p6 ∨ p6) ∨ (p2 ∨ True))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p5 p1 p4 p0 p2 p3 p7 : Prop)
theorem file86_103733 : (((((p7 → p3) → False) → ((False ∨ False) → False)) ∨ (((p1 → p2) ∨ (p1 → False)) → ((p0 → False) ∨ (p0 ∨ p4)))) ∨ ((((p1 ∧ p1) → False) → ((p2 ∧ p5) → (p2 → p3))) ∨ (((p0 ∨ p7) ∧ (False ∧ p2)) ∨ ((p1 ∧ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply False.elim assump_3
  case inr assump_4 =>
    apply False.elim assump_4


variable (p7 p2 p6 p5 p3 : Prop)
theorem file86_104204 : (((((True → False) → False) → ((p3 ∧ p5) ∨ (True ∧ p5))) ∧ (((True → False) ∧ (p6 ∨ p3)) ∧ ((p7 ∧ p6) → (p7 → True)))) → ((((True → False) → False) → ((False ∨ p6) ∨ (p6 → False))) ∧ (((p2 ∧ True) ∨ (True → False)) ∨ ((p7 ∧ p6) → False)))) := by
  intro assump_16
  apply And.intro
  intro assump_17
  cases assump_16
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_27
        case inl assump_30 =>
          apply Or.inl
          apply Or.inr
          exact assump_30
        case inr assump_31 =>
          apply Or.inr
          intro assump_40
          have assump_88 : True := by
            apply True.intro
          let assump_46 := assump_26 assump_88
          apply False.elim assump_46
  cases assump_16
  case intro assump_50 assump_51 =>
    cases assump_51
    case intro assump_54 assump_55 =>
      cases assump_54
      case intro assump_56 assump_57 =>
        cases assump_57
        case inl assump_60 =>
          apply Or.inl
          apply Or.inr
          intro assump_66
          have assump_89 : True := by
            apply True.intro
          let assump_71 := assump_56 assump_89
          apply False.elim assump_71
        case inr assump_61 =>
          apply Or.inl
          apply Or.inr
          intro assump_79
          have assump_90 : True := by
            apply True.intro
          let assump_84 := assump_56 assump_90
          apply False.elim assump_84


variable (p6 p4 p3 p2 p1 p5 p7 : Prop)
theorem file86_105801 : (((((False ∧ p1) ∧ (False → False)) ∧ ((p6 → False) ∧ (p4 ∨ p1))) ∨ (((p2 ∨ True) → False) → ((p4 ∨ p6) ∧ (p4 ∧ p7)))) ∨ ((((p5 ∧ p3) → (True → False)) → ((p1 → p5) → (True ∧ p1))) → False)) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply And.intro
  have assump_20 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4
  apply And.intro
  have assump_21 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_10 := assump_1 assump_21
  apply False.elim assump_10
  have assump_22 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_16 := assump_1 assump_22
  apply False.elim assump_16


variable (p4 p7 p5 p3 p1 p2 : Prop)
theorem file86_106565 : (((((True → p1) ∨ (p2 → False)) ∨ ((False → False) ∧ (True ∧ p7))) ∧ (((p7 → p5) → (True ∨ p4)) → False)) → ((((p3 ∨ p5) ∨ (True ∨ p4)) ∨ ((True ∧ p5) → False)) ∨ (((p7 ∨ p1) → False) → ((p4 ∨ p1) ∨ (p4 ∧ False))))) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
      case inr assump_14 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
    case inr assump_12 =>
      cases assump_12
      case intro assump_23 assump_24 =>
        cases assump_24
        case intro assump_27 assump_28 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply True.intro


variable (p3 p6 p7 p4 p5 p0 : Prop)
theorem file86_107530 : (((((p0 → p6) → (p0 → p3)) ∧ ((p0 ∨ p7) → False)) ∧ (((p4 → False) ∧ (False ∧ p6)) ∧ ((p7 ∧ p3) ∧ (p5 ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply False.elim assump_16


variable (p1 p7 p3 : Prop)
theorem file86_108069 : ((((((p7 → False) → False) → False) → (((True → False) → False) ∨ ((p3 → False) ∨ (p1 ∨ p1)))) → False) → False) := by
  intro assump_14
  have assump_31 : ((((p7 → False) → False) → False) → (((True → False) → False) ∨ ((p3 → False) ∨ (p1 ∨ p1)))) := by
    intro assump_18
    apply Or.inl
    intro assump_21
    have assump_32 : True := by
      apply True.intro
    let assump_24 := assump_21 assump_32
    apply False.elim assump_24
  let assump_17 := assump_14 assump_31
  apply False.elim assump_17


variable (p7 p5 : Prop)
theorem file86_108624 : (((((p5 → False) ∨ (p7 ∧ p7)) → ((False → p7) ∨ (True → p7))) → False) → False) := by
  intro assump_1
  have assump_25 : (((p5 → False) ∨ (p7 ∧ p7)) → ((False → p7) ∨ (True → p7))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_13 assump_14 =>
        apply Or.inl
        intro assump_19
        apply False.elim assump_19
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p4 p0 p3 p5 p7 p2 : Prop)
theorem file86_109243 : ((((((False ∨ p2) ∨ (p2 ∨ p4)) ∨ ((p5 → False) → False)) → (((p0 ∧ p6) ∨ (p3 ∧ p7)) ∨ ((False → p5) ∨ (p5 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((False ∨ p2) ∨ (p2 ∨ p4)) ∨ ((p5 → False) → False)) → (((p0 ∧ p6) ∨ (p3 ∧ p7)) ∨ ((False → p5) ∨ (p5 ∨ p4)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          apply Or.inr
          apply Or.inl
          intro assump_16
          apply False.elim assump_16
      case inr assump_9 =>
        cases assump_9
        case inl assump_19 =>
          apply Or.inr
          apply Or.inl
          intro assump_23
          apply False.elim assump_23
        case inr assump_20 =>
          apply Or.inr
          apply Or.inl
          intro assump_28
          apply False.elim assump_28
    case inr assump_7 =>
      apply Or.inr
      apply Or.inl
      intro assump_33
      apply False.elim assump_33
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p3 p1 p7 p4 p5 : Prop)
theorem file86_110445 : ((((((False → False) → (p7 ∧ p5)) → ((p4 → p3) ∨ (True ∧ False))) → (((True → False) ∨ (p7 ∧ p5)) → ((False ∨ p1) → (p1 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((False → False) → (p7 ∧ p5)) → ((p4 → p3) ∨ (True ∧ False))) → (((True → False) ∨ (p7 ∧ p5)) → ((False ∨ p1) → (p1 ∨ p1)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      apply False.elim assump_8
    case inr assump_9 =>
      cases assump_6
      case inl assump_14 =>
        apply Or.inl
        exact assump_9
      case inr assump_15 =>
        cases assump_15
        case intro assump_20 assump_21 =>
          apply Or.inl
          exact assump_9
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p2 p4 p5 p0 p3 : Prop)
theorem file86_111282 : ((((((p3 ∧ p4) ∧ (p2 → p4)) ∨ ((False → False) ∨ (p3 → False))) ∨ (((p5 ∨ p3) ∧ (p0 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 ∧ p4) ∧ (p2 → p4)) ∨ ((False → False) ∨ (p3 → False))) ∨ (((p5 ∨ p3) ∧ (p0 ∧ False)) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p7 p1 p4 p5 p2 p3 : Prop)
theorem file86_111782 : (((((p2 → False) → (False → False)) → False) → (((p2 → False) → False) ∧ ((p4 → False) ∧ (p0 → False)))) ∧ ((((p5 → p5) ∨ (p3 → p1)) → ((p7 ∧ False) → (False → False))) ∨ (((p5 → p7) ∧ (p4 → True)) → False))) := by
  apply And.intro
  intro assump_13
  apply And.intro
  intro assump_14
  have assump_58 : ((p2 → False) → (False → False)) := by
    intro assump_20
    intro assump_21
    apply False.elim assump_21
  let assump_19 := assump_13 assump_58
  apply False.elim assump_19
  apply And.intro
  intro assump_27
  have assump_59 : ((p2 → False) → (False → False)) := by
    intro assump_33
    intro assump_34
    apply False.elim assump_34
  let assump_32 := assump_13 assump_59
  apply False.elim assump_32
  intro assump_40
  have assump_60 : ((p2 → False) → (False → False)) := by
    intro assump_46
    intro assump_47
    apply False.elim assump_47
  let assump_45 := assump_13 assump_60
  apply False.elim assump_45
  apply Or.inl
  intro assump_53
  intro assump_54
  intro assump_55
  apply False.elim assump_55


variable (p2 p7 p6 p5 p4 p1 : Prop)
theorem file86_112872 : ((((((p5 ∨ p7) ∨ (p7 ∧ p6)) ∧ ((p4 → False) ∨ (p2 ∧ p5))) ∧ (((True → False) → (False → False)) → False)) ∧ ((((p1 ∧ p4) ∧ (p5 ∨ False)) ∧ ((False → False) ∧ (p1 → p2))) → (((False ∨ True) → (True → p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case inl assump_14 =>
              have assump_130 : ((True → False) → (False → False)) := by
                intro assump_24
                intro assump_25
                apply False.elim assump_25
              let assump_23 := assump_5 assump_130
              apply False.elim assump_23
            case inr assump_15 =>
              cases assump_15
              case intro assump_31 assump_32 =>
                have assump_131 : ((True → False) → (False → False)) := by
                  intro assump_43
                  intro assump_44
                  apply False.elim assump_44
                let assump_42 := assump_5 assump_131
                apply False.elim assump_42
          case inr assump_11 =>
            cases assump_7
            case inl assump_52 =>
              have assump_132 : ((True → False) → (False → False)) := by
                intro assump_62
                intro assump_63
                apply False.elim assump_63
              let assump_61 := assump_5 assump_132
              apply False.elim assump_61
            case inr assump_53 =>
              cases assump_53
              case intro assump_69 assump_70 =>
                have assump_133 : ((True → False) → (False → False)) := by
                  intro assump_81
                  intro assump_82
                  apply False.elim assump_82
                let assump_80 := assump_5 assump_133
                apply False.elim assump_80
        case inr assump_9 =>
          cases assump_9
          case intro assump_88 assump_89 =>
            cases assump_7
            case inl assump_94 =>
              have assump_134 : ((True → False) → (False → False)) := by
                intro assump_104
                intro assump_105
                apply False.elim assump_105
              let assump_103 := assump_5 assump_134
              apply False.elim assump_103
            case inr assump_95 =>
              cases assump_95
              case intro assump_111 assump_112 =>
                have assump_135 : ((True → False) → (False → False)) := by
                  intro assump_123
                  intro assump_124
                  apply False.elim assump_124
                let assump_122 := assump_5 assump_135
                apply False.elim assump_122


variable (p2 p1 p5 p4 p6 p0 p7 : Prop)
theorem file86_115785 : (((((p2 ∨ p5) ∨ (p0 → False)) ∧ ((p0 → p4) → False)) ∧ (((p1 ∨ p1) → False) ∧ ((p4 ∨ False) ∧ (True ∧ p7)))) → ((((p0 → False) ∨ (p1 ∨ p7)) → False) → (((p6 ∨ p4) ∨ (p7 → p2)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_13
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case inl assump_30 =>
                    cases assump_29
                    case intro assump_34 assump_35 =>
                      have assump_332 : (p0 → p4) := by
                        intro assump_44
                        exact assump_30
                      let assump_43 := assump_15 assump_332
                      apply False.elim assump_43
                  case inr assump_31 =>
                    apply False.elim assump_31
            case inr assump_19 =>
              cases assump_13
              case intro assump_56 assump_57 =>
                cases assump_57
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case inl assump_62 =>
                    cases assump_61
                    case intro assump_66 assump_67 =>
                      have assump_333 : (p0 → p4) := by
                        intro assump_76
                        exact assump_62
                      let assump_75 := assump_15 assump_333
                      apply False.elim assump_75
                  case inr assump_63 =>
                    apply False.elim assump_63
          case inr assump_17 =>
            cases assump_13
            case intro assump_88 assump_89 =>
              cases assump_89
              case intro assump_92 assump_93 =>
                cases assump_92
                case inl assump_94 =>
                  cases assump_93
                  case intro assump_98 assump_99 =>
                    have assump_334 : (p0 → p4) := by
                      intro assump_108
                      exact assump_94
                    let assump_107 := assump_15 assump_334
                    apply False.elim assump_107
                case inr assump_95 =>
                  apply False.elim assump_95
    case inr assump_7 =>
      cases assump_1
      case intro assump_120 assump_121 =>
        cases assump_120
        case intro assump_122 assump_123 =>
          cases assump_122
          case inl assump_124 =>
            cases assump_124
            case inl assump_126 =>
              cases assump_121
              case intro assump_132 assump_133 =>
                cases assump_133
                case intro assump_136 assump_137 =>
                  cases assump_136
                  case inl assump_138 =>
                    cases assump_137
                    case intro assump_142 assump_143 =>
                      have assump_335 : (p0 → p4) := by
                        intro assump_152
                        exact assump_138
                      let assump_151 := assump_123 assump_335
                      apply False.elim assump_151
                  case inr assump_139 =>
                    apply False.elim assump_139
            case inr assump_127 =>
              cases assump_121
              case intro assump_164 assump_165 =>
                cases assump_165
                case intro assump_168 assump_169 =>
                  cases assump_168
                  case inl assump_170 =>
                    cases assump_169
                    case intro assump_174 assump_175 =>
                      have assump_336 : (p0 → p4) := by
                        intro assump_184
                        exact assump_170
                      let assump_183 := assump_123 assump_336
                      apply False.elim assump_183
                  case inr assump_171 =>
                    apply False.elim assump_171
          case inr assump_125 =>
            cases assump_121
            case intro assump_196 assump_197 =>
              cases assump_197
              case intro assump_200 assump_201 =>
                cases assump_200
                case inl assump_202 =>
                  cases assump_201
                  case intro assump_206 assump_207 =>
                    have assump_337 : (p0 → p4) := by
                      intro assump_216
                      exact assump_202
                    let assump_215 := assump_123 assump_337
                    apply False.elim assump_215
                case inr assump_203 =>
                  apply False.elim assump_203
  case inr assump_5 =>
    cases assump_1
    case intro assump_228 assump_229 =>
      cases assump_228
      case intro assump_230 assump_231 =>
        cases assump_230
        case inl assump_232 =>
          cases assump_232
          case inl assump_234 =>
            cases assump_229
            case intro assump_240 assump_241 =>
              cases assump_241
              case intro assump_244 assump_245 =>
                cases assump_244
                case inl assump_246 =>
                  cases assump_245
                  case intro assump_250 assump_251 =>
                    have assump_338 : (p0 → p4) := by
                      intro assump_260
                      exact assump_246
                    let assump_259 := assump_231 assump_338
                    apply False.elim assump_259
                case inr assump_247 =>
                  apply False.elim assump_247
          case inr assump_235 =>
            cases assump_229
            case intro assump_272 assump_273 =>
              cases assump_273
              case intro assump_276 assump_277 =>
                cases assump_276
                case inl assump_278 =>
                  cases assump_277
                  case intro assump_282 assump_283 =>
                    have assump_339 : (p0 → p4) := by
                      intro assump_292
                      exact assump_278
                    let assump_291 := assump_231 assump_339
                    apply False.elim assump_291
                case inr assump_279 =>
                  apply False.elim assump_279
        case inr assump_233 =>
          cases assump_229
          case intro assump_304 assump_305 =>
            cases assump_305
            case intro assump_308 assump_309 =>
              cases assump_308
              case inl assump_310 =>
                cases assump_309
                case intro assump_314 assump_315 =>
                  have assump_340 : (p0 → p4) := by
                    intro assump_324
                    exact assump_310
                  let assump_323 := assump_231 assump_340
                  apply False.elim assump_323
              case inr assump_311 =>
                apply False.elim assump_311


variable (p3 p6 p7 p0 p2 p5 : Prop)
theorem file86_122997 : ((((((False ∧ p7) ∧ (p5 → False)) → ((p5 → p7) → (p5 ∨ p6))) ∨ (((p3 → False) → (p2 ∧ p6)) ∨ ((p0 ∨ p0) → (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False ∧ p7) ∧ (p5 → False)) → ((p5 → p7) → (p5 ∨ p6))) ∨ (((p3 → False) → (p2 ∧ p6)) ∨ ((p0 ∨ p0) → (p3 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p3 p6 p4 p2 p1 p0 p7 : Prop)
theorem file86_123643 : (((((True → False) ∧ (False ∨ p5)) ∧ ((p3 → False) → (p3 → p2))) → (((p3 ∨ p0) ∨ (p3 ∧ p5)) ∨ ((p2 ∨ p6) ∧ (p0 → p2)))) → ((((p2 ∧ p5) → (p3 → True)) ∨ ((p5 → False) → (p2 ∨ p4))) ∧ (((p4 ∧ p7) → (p7 ∨ p7)) ∧ ((p0 ∨ True) ∨ (p6 ∨ p1))))) := by
  intro assump_25
  apply And.intro
  apply Or.inl
  intro assump_28
  intro assump_29
  apply True.intro
  apply And.intro
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    apply Or.inl
    exact assump_32
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p5 p0 p6 : Prop)
theorem file86_124220 : (((((True ∨ p6) → False) → ((p0 ∧ p5) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : (((True ∨ p6) → False) → ((p0 ∧ p5) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_23 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_15 := assump_5 assump_23
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p6 p0 p3 p4 : Prop)
theorem file86_124757 : ((((((p7 → p3) ∧ (p0 ∨ p7)) → ((p3 → False) → (p6 ∨ True))) ∨ (((p0 → False) → False) ∨ ((p4 → False) ∧ (p3 ∨ p7)))) → False) → False) := by
  intro assump_22
  have assump_43 : ((((p7 → p3) ∧ (p0 ∨ p7)) → ((p3 → False) → (p6 ∨ True))) ∨ (((p0 → False) → False) ∨ ((p4 → False) ∧ (p3 ∨ p7)))) := by
    apply Or.inl
    intro assump_26
    intro assump_27
    cases assump_26
    case intro assump_30 assump_31 =>
      cases assump_31
      case inl assump_34 =>
        apply Or.inr
        apply True.intro
      case inr assump_35 =>
        apply Or.inr
        apply True.intro
  let assump_25 := assump_22 assump_43
  apply False.elim assump_25


variable (p5 p4 : Prop)
theorem file86_125457 : (((((p4 → False) ∧ (False ∨ p5)) → ((True ∨ p4) ∨ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p4 → False) ∧ (False ∨ p5)) → ((True ∨ p4) ∨ (p5 → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply False.elim assump_10
      case inr assump_11 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p1 p3 p2 p5 : Prop)
theorem file86_126026 : ((((((True ∧ True) → False) → ((p1 → False) → False)) ∨ (((p5 ∨ p3) → (p2 → p2)) → ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True ∧ True) → False) → ((p1 → False) → False)) ∨ (((p5 ∨ p3) → (p2 → p2)) → ((p7 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : (True ∧ True) := by
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p4 p3 p6 p0 p7 p2 : Prop)
theorem file86_126669 : (((((p4 → False) ∧ (p0 → p6)) ∧ ((p1 ∨ False) ∨ (p4 ∨ p3))) → (((p3 ∧ p7) ∨ (p1 ∨ p7)) → ((p3 → False) → (False → p3)))) ∨ ((((False → p6) ∧ (p4 → False)) ∧ ((p3 → p1) → False)) ∨ (((p4 ∧ p2) ∧ (True → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p7 p1 p5 p2 p4 p0 p6 p3 : Prop)
theorem file86_127073 : (((((p4 ∧ p0) ∧ (p5 → False)) ∧ ((p1 → True) ∧ (p6 ∧ False))) → (((False ∨ p2) ∨ (p3 → False)) ∧ ((p0 ∨ p2) → (p7 ∨ p2)))) ∨ ((((p1 → False) → False) ∨ ((p4 ∧ p3) ∨ (p7 ∧ False))) ∧ (((p2 → p4) ∧ (p6 ∧ p1)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
  intro assump_24
  cases assump_24
  case inl assump_25 =>
    cases assump_1
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          cases assump_30
          case intro assump_41 assump_42 =>
            cases assump_42
            case intro assump_45 assump_46 =>
              apply False.elim assump_46
  case inr assump_26 =>
    cases assump_1
    case intro assump_53 assump_54 =>
      cases assump_53
      case intro assump_55 assump_56 =>
        cases assump_55
        case intro assump_57 assump_58 =>
          cases assump_54
          case intro assump_65 assump_66 =>
            cases assump_66
            case intro assump_69 assump_70 =>
              apply False.elim assump_70


variable (p6 p7 p3 p4 p2 p0 : Prop)
theorem file86_128570 : ((((((p7 → False) ∨ (p2 ∨ False)) → False) ∧ (((True → False) → (p3 → False)) ∧ ((p3 ∨ p0) → (p6 ∧ p6)))) ∧ ((((False → False) ∨ (p2 ∧ p4)) ∨ ((False → p6) ∧ (p3 → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_23 : (((False → False) ∨ (p2 ∧ p4)) ∨ ((False → p6) ∧ (p3 → p2))) := by
          apply Or.inl
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p1 p6 p0 : Prop)
theorem file86_129278 : (((((True → False) → (p0 ∨ False)) ∨ ((p6 → False) → False)) ∧ (((p1 ∧ True) ∨ (p1 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_22 : ((p1 ∧ True) ∨ (p1 ∨ True)) := by
        apply Or.inr
        apply Or.inr
        apply True.intro
      let assump_10 := assump_3 assump_22
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_23 : ((p1 ∧ True) ∨ (p1 ∨ True)) := by
        apply Or.inr
        apply Or.inr
        apply True.intro
      let assump_18 := assump_3 assump_23
      apply False.elim assump_18


