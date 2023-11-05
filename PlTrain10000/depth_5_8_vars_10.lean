variable (p4 p5 p2 p6 p3 p7 : Prop)
theorem file10_44 : ((((((p6 ∧ p6) ∧ (False ∧ p2)) ∧ ((p5 → False) → (True ∨ p2))) ∨ (((True → False) → (p7 ∨ p5)) ∨ ((p3 → p4) ∧ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 ∧ p6) ∧ (False ∧ p2)) ∧ ((p5 → False) → (True ∨ p2))) ∨ (((True → False) → (p7 ∨ p5)) ∨ ((p3 → p4) ∧ (p6 → False)))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p7 p0 p5 p1 p3 p6 p4 : Prop)
theorem file10_668 : (((((p5 → p3) → False) ∧ ((True → p3) ∧ (p5 ∨ p0))) → False) ∧ ((((False ∧ p7) ∧ (p1 → p6)) → ((True → False) ∨ (False ∧ p2))) ∨ (((p5 ∧ False) → False) ∧ ((p4 → False) ∨ (p3 ∧ p7))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_51 : (p5 → p3) := by
          intro assump_18
          have assump_52 : True := by
            apply True.intro
          let assump_23 := assump_6 assump_52
          exact assump_23
        let assump_17 := assump_2 assump_51
        apply False.elim assump_17
      case inr assump_11 =>
        have assump_53 : (p5 → p3) := by
          intro assump_34
          have assump_54 : True := by
            apply True.intro
          let assump_39 := assump_6 assump_54
          exact assump_39
        let assump_33 := assump_2 assump_53
        apply False.elim assump_33
  apply Or.inl
  intro assump_44
  cases assump_44
  case intro assump_45 assump_46 =>
    cases assump_45
    case intro assump_47 assump_48 =>
      apply False.elim assump_47


variable (p5 p2 p1 p0 p7 p3 p6 : Prop)
theorem file10_1888 : (((((p7 ∨ p6) ∨ (p5 ∧ p1)) → ((p0 → False) → False)) → (((p2 ∨ False) ∧ (True → p5)) → ((p0 ∧ p2) ∨ (p3 ∨ p2)))) ∨ ((((False ∨ p6) ∨ (False ∧ p2)) → ((p6 ∧ p6) ∨ (p0 ∨ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inr
      apply Or.inr
      exact assump_5
    case inr assump_6 =>
      apply False.elim assump_6


variable (p1 p2 p0 p5 p7 : Prop)
theorem file10_2395 : ((((((p5 ∨ p7) ∧ (p7 → p1)) ∧ ((False ∧ p1) ∨ (p1 ∨ p5))) ∨ (((p2 → False) ∧ (True → False)) → ((p7 ∧ p7) ∧ (p5 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p5 ∨ p7) ∧ (p7 → p1)) ∧ ((False ∧ p1) ∨ (p1 ∨ p5))) ∨ (((p2 → False) ∧ (True → False)) → ((p7 ∧ p7) ∧ (p5 ∧ p0)))) := by
    apply Or.inr
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_50 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_50
      apply False.elim assump_12
    cases assump_5
    case intro assump_16 assump_17 =>
      have assump_51 : True := by
        apply True.intro
      let assump_22 := assump_17 assump_51
      apply False.elim assump_22
    apply And.intro
    cases assump_5
    case intro assump_26 assump_27 =>
      have assump_52 : True := by
        apply True.intro
      let assump_32 := assump_27 assump_52
      apply False.elim assump_32
    cases assump_5
    case intro assump_36 assump_37 =>
      have assump_53 : True := by
        apply True.intro
      let assump_42 := assump_37 assump_53
      apply False.elim assump_42
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p1 p3 p6 p0 p5 p7 : Prop)
theorem file10_3687 : (((((p0 ∧ p1) ∧ (p5 ∨ p5)) → ((True → p6) ∨ (p7 → False))) ∧ (((False ∧ p3) ∨ (False → p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False ∧ p3) ∨ (False → p1)) := by
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p7 p6 p0 p3 : Prop)
theorem file10_4124 : (((((p6 ∨ True) → (p7 ∨ p6)) → ((False → False) → (p0 ∨ p3))) ∧ (((p7 ∧ p6) ∨ (False → False)) → False)) → ((((p7 ∨ True) → False) → ((p0 → p6) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_18 : ((p7 ∧ p6) ∨ (False → False)) := by
      apply Or.inr
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_6 assump_18
    apply False.elim assump_11


variable (p0 p3 p6 p2 p1 p4 p7 p5 : Prop)
theorem file10_4647 : ((((((p6 ∧ p6) ∨ (p2 → False)) ∧ ((p2 → p6) ∨ (p6 → False))) ∧ (((p1 ∧ p7) → (p6 → p4)) ∨ ((False → False) ∨ (p5 ∧ True)))) ∧ ((((p6 ∧ p7) ∨ (p4 → p4)) → False) ∧ (((p0 → p3) ∧ (p1 ∨ p6)) ∨ ((p5 ∨ p2) ∨ (p3 ∧ p1))))) → False) := by
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
          case intro assump_10 assump_11 =>
            cases assump_7
            case inl assump_16 =>
              cases assump_5
              case inl assump_20 =>
                cases assump_3
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case inl assump_28 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_31
                      case inl assump_34 =>
                        have assump_962 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_41
                          exact assump_41
                        let assump_40 := assump_24 assump_962
                        apply False.elim assump_40
                      case inr assump_35 =>
                        have assump_963 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_52
                          exact assump_52
                        let assump_51 := assump_24 assump_963
                        apply False.elim assump_51
                  case inr assump_29 =>
                    cases assump_29
                    case inl assump_58 =>
                      cases assump_58
                      case inl assump_60 =>
                        have assump_964 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_66
                          exact assump_66
                        let assump_65 := assump_24 assump_964
                        apply False.elim assump_65
                      case inr assump_61 =>
                        have assump_965 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_76
                          exact assump_76
                        let assump_75 := assump_24 assump_965
                        apply False.elim assump_75
                    case inr assump_59 =>
                      cases assump_59
                      case intro assump_82 assump_83 =>
                        have assump_966 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_91
                          exact assump_91
                        let assump_90 := assump_24 assump_966
                        apply False.elim assump_90
              case inr assump_21 =>
                cases assump_21
                case inl assump_97 =>
                  cases assump_3
                  case intro assump_101 assump_102 =>
                    cases assump_102
                    case inl assump_105 =>
                      cases assump_105
                      case intro assump_107 assump_108 =>
                        cases assump_108
                        case inl assump_111 =>
                          have assump_967 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_118
                            exact assump_118
                          let assump_117 := assump_101 assump_967
                          apply False.elim assump_117
                        case inr assump_112 =>
                          have assump_968 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_129
                            exact assump_129
                          let assump_128 := assump_101 assump_968
                          apply False.elim assump_128
                    case inr assump_106 =>
                      cases assump_106
                      case inl assump_135 =>
                        cases assump_135
                        case inl assump_137 =>
                          have assump_969 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_143
                            exact assump_143
                          let assump_142 := assump_101 assump_969
                          apply False.elim assump_142
                        case inr assump_138 =>
                          have assump_970 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_153
                            exact assump_153
                          let assump_152 := assump_101 assump_970
                          apply False.elim assump_152
                      case inr assump_136 =>
                        cases assump_136
                        case intro assump_159 assump_160 =>
                          have assump_971 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_168
                            exact assump_168
                          let assump_167 := assump_101 assump_971
                          apply False.elim assump_167
                case inr assump_98 =>
                  cases assump_98
                  case intro assump_174 assump_175 =>
                    cases assump_3
                    case intro assump_180 assump_181 =>
                      cases assump_181
                      case inl assump_184 =>
                        cases assump_184
                        case intro assump_186 assump_187 =>
                          cases assump_187
                          case inl assump_190 =>
                            have assump_972 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_197
                              exact assump_197
                            let assump_196 := assump_180 assump_972
                            apply False.elim assump_196
                          case inr assump_191 =>
                            have assump_973 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_208
                              exact assump_208
                            let assump_207 := assump_180 assump_973
                            apply False.elim assump_207
                      case inr assump_185 =>
                        cases assump_185
                        case inl assump_214 =>
                          cases assump_214
                          case inl assump_216 =>
                            have assump_974 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_222
                              exact assump_222
                            let assump_221 := assump_180 assump_974
                            apply False.elim assump_221
                          case inr assump_217 =>
                            have assump_975 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_232
                              exact assump_232
                            let assump_231 := assump_180 assump_975
                            apply False.elim assump_231
                        case inr assump_215 =>
                          cases assump_215
                          case intro assump_238 assump_239 =>
                            have assump_976 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_247
                              exact assump_247
                            let assump_246 := assump_180 assump_976
                            apply False.elim assump_246
            case inr assump_17 =>
              cases assump_5
              case inl assump_255 =>
                cases assump_3
                case intro assump_259 assump_260 =>
                  cases assump_260
                  case inl assump_263 =>
                    cases assump_263
                    case intro assump_265 assump_266 =>
                      cases assump_266
                      case inl assump_269 =>
                        have assump_977 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_276
                          exact assump_276
                        let assump_275 := assump_259 assump_977
                        apply False.elim assump_275
                      case inr assump_270 =>
                        have assump_978 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_287
                          exact assump_287
                        let assump_286 := assump_259 assump_978
                        apply False.elim assump_286
                  case inr assump_264 =>
                    cases assump_264
                    case inl assump_293 =>
                      cases assump_293
                      case inl assump_295 =>
                        have assump_979 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_301
                          exact assump_301
                        let assump_300 := assump_259 assump_979
                        apply False.elim assump_300
                      case inr assump_296 =>
                        have assump_980 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_311
                          exact assump_311
                        let assump_310 := assump_259 assump_980
                        apply False.elim assump_310
                    case inr assump_294 =>
                      cases assump_294
                      case intro assump_317 assump_318 =>
                        have assump_981 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_326
                          exact assump_326
                        let assump_325 := assump_259 assump_981
                        apply False.elim assump_325
              case inr assump_256 =>
                cases assump_256
                case inl assump_332 =>
                  cases assump_3
                  case intro assump_336 assump_337 =>
                    cases assump_337
                    case inl assump_340 =>
                      cases assump_340
                      case intro assump_342 assump_343 =>
                        cases assump_343
                        case inl assump_346 =>
                          have assump_982 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_353
                            exact assump_353
                          let assump_352 := assump_336 assump_982
                          apply False.elim assump_352
                        case inr assump_347 =>
                          have assump_983 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_364
                            exact assump_364
                          let assump_363 := assump_336 assump_983
                          apply False.elim assump_363
                    case inr assump_341 =>
                      cases assump_341
                      case inl assump_370 =>
                        cases assump_370
                        case inl assump_372 =>
                          have assump_984 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_378
                            exact assump_378
                          let assump_377 := assump_336 assump_984
                          apply False.elim assump_377
                        case inr assump_373 =>
                          have assump_985 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_388
                            exact assump_388
                          let assump_387 := assump_336 assump_985
                          apply False.elim assump_387
                      case inr assump_371 =>
                        cases assump_371
                        case intro assump_394 assump_395 =>
                          have assump_986 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_403
                            exact assump_403
                          let assump_402 := assump_336 assump_986
                          apply False.elim assump_402
                case inr assump_333 =>
                  cases assump_333
                  case intro assump_409 assump_410 =>
                    cases assump_3
                    case intro assump_415 assump_416 =>
                      cases assump_416
                      case inl assump_419 =>
                        cases assump_419
                        case intro assump_421 assump_422 =>
                          cases assump_422
                          case inl assump_425 =>
                            have assump_987 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_432
                              exact assump_432
                            let assump_431 := assump_415 assump_987
                            apply False.elim assump_431
                          case inr assump_426 =>
                            have assump_988 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_443
                              exact assump_443
                            let assump_442 := assump_415 assump_988
                            apply False.elim assump_442
                      case inr assump_420 =>
                        cases assump_420
                        case inl assump_449 =>
                          cases assump_449
                          case inl assump_451 =>
                            have assump_989 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_457
                              exact assump_457
                            let assump_456 := assump_415 assump_989
                            apply False.elim assump_456
                          case inr assump_452 =>
                            have assump_990 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_467
                              exact assump_467
                            let assump_466 := assump_415 assump_990
                            apply False.elim assump_466
                        case inr assump_450 =>
                          cases assump_450
                          case intro assump_473 assump_474 =>
                            have assump_991 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                              apply Or.inr
                              intro assump_482
                              exact assump_482
                            let assump_481 := assump_415 assump_991
                            apply False.elim assump_481
        case inr assump_9 =>
          cases assump_7
          case inl assump_490 =>
            cases assump_5
            case inl assump_494 =>
              cases assump_3
              case intro assump_498 assump_499 =>
                cases assump_499
                case inl assump_502 =>
                  cases assump_502
                  case intro assump_504 assump_505 =>
                    cases assump_505
                    case inl assump_508 =>
                      have assump_992 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_515
                        exact assump_515
                      let assump_514 := assump_498 assump_992
                      apply False.elim assump_514
                    case inr assump_509 =>
                      have assump_993 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_526
                        exact assump_526
                      let assump_525 := assump_498 assump_993
                      apply False.elim assump_525
                case inr assump_503 =>
                  cases assump_503
                  case inl assump_532 =>
                    cases assump_532
                    case inl assump_534 =>
                      have assump_994 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_540
                        exact assump_540
                      let assump_539 := assump_498 assump_994
                      apply False.elim assump_539
                    case inr assump_535 =>
                      have assump_995 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_550
                        exact assump_550
                      let assump_549 := assump_498 assump_995
                      apply False.elim assump_549
                  case inr assump_533 =>
                    cases assump_533
                    case intro assump_556 assump_557 =>
                      have assump_996 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_565
                        exact assump_565
                      let assump_564 := assump_498 assump_996
                      apply False.elim assump_564
            case inr assump_495 =>
              cases assump_495
              case inl assump_571 =>
                cases assump_3
                case intro assump_575 assump_576 =>
                  cases assump_576
                  case inl assump_579 =>
                    cases assump_579
                    case intro assump_581 assump_582 =>
                      cases assump_582
                      case inl assump_585 =>
                        have assump_997 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_592
                          exact assump_592
                        let assump_591 := assump_575 assump_997
                        apply False.elim assump_591
                      case inr assump_586 =>
                        have assump_998 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_603
                          exact assump_603
                        let assump_602 := assump_575 assump_998
                        apply False.elim assump_602
                  case inr assump_580 =>
                    cases assump_580
                    case inl assump_609 =>
                      cases assump_609
                      case inl assump_611 =>
                        have assump_999 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_617
                          exact assump_617
                        let assump_616 := assump_575 assump_999
                        apply False.elim assump_616
                      case inr assump_612 =>
                        have assump_1000 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_627
                          exact assump_627
                        let assump_626 := assump_575 assump_1000
                        apply False.elim assump_626
                    case inr assump_610 =>
                      cases assump_610
                      case intro assump_633 assump_634 =>
                        have assump_1001 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_642
                          exact assump_642
                        let assump_641 := assump_575 assump_1001
                        apply False.elim assump_641
              case inr assump_572 =>
                cases assump_572
                case intro assump_648 assump_649 =>
                  cases assump_3
                  case intro assump_654 assump_655 =>
                    cases assump_655
                    case inl assump_658 =>
                      cases assump_658
                      case intro assump_660 assump_661 =>
                        cases assump_661
                        case inl assump_664 =>
                          have assump_1002 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_671
                            exact assump_671
                          let assump_670 := assump_654 assump_1002
                          apply False.elim assump_670
                        case inr assump_665 =>
                          have assump_1003 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_682
                            exact assump_682
                          let assump_681 := assump_654 assump_1003
                          apply False.elim assump_681
                    case inr assump_659 =>
                      cases assump_659
                      case inl assump_688 =>
                        cases assump_688
                        case inl assump_690 =>
                          have assump_1004 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_696
                            exact assump_696
                          let assump_695 := assump_654 assump_1004
                          apply False.elim assump_695
                        case inr assump_691 =>
                          have assump_1005 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_706
                            exact assump_706
                          let assump_705 := assump_654 assump_1005
                          apply False.elim assump_705
                      case inr assump_689 =>
                        cases assump_689
                        case intro assump_712 assump_713 =>
                          have assump_1006 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_721
                            exact assump_721
                          let assump_720 := assump_654 assump_1006
                          apply False.elim assump_720
          case inr assump_491 =>
            cases assump_5
            case inl assump_729 =>
              cases assump_3
              case intro assump_733 assump_734 =>
                cases assump_734
                case inl assump_737 =>
                  cases assump_737
                  case intro assump_739 assump_740 =>
                    cases assump_740
                    case inl assump_743 =>
                      have assump_1007 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_750
                        exact assump_750
                      let assump_749 := assump_733 assump_1007
                      apply False.elim assump_749
                    case inr assump_744 =>
                      have assump_1008 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_761
                        exact assump_761
                      let assump_760 := assump_733 assump_1008
                      apply False.elim assump_760
                case inr assump_738 =>
                  cases assump_738
                  case inl assump_767 =>
                    cases assump_767
                    case inl assump_769 =>
                      have assump_1009 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_775
                        exact assump_775
                      let assump_774 := assump_733 assump_1009
                      apply False.elim assump_774
                    case inr assump_770 =>
                      have assump_1010 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_785
                        exact assump_785
                      let assump_784 := assump_733 assump_1010
                      apply False.elim assump_784
                  case inr assump_768 =>
                    cases assump_768
                    case intro assump_791 assump_792 =>
                      have assump_1011 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                        apply Or.inr
                        intro assump_800
                        exact assump_800
                      let assump_799 := assump_733 assump_1011
                      apply False.elim assump_799
            case inr assump_730 =>
              cases assump_730
              case inl assump_806 =>
                cases assump_3
                case intro assump_810 assump_811 =>
                  cases assump_811
                  case inl assump_814 =>
                    cases assump_814
                    case intro assump_816 assump_817 =>
                      cases assump_817
                      case inl assump_820 =>
                        have assump_1012 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_827
                          exact assump_827
                        let assump_826 := assump_810 assump_1012
                        apply False.elim assump_826
                      case inr assump_821 =>
                        have assump_1013 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_838
                          exact assump_838
                        let assump_837 := assump_810 assump_1013
                        apply False.elim assump_837
                  case inr assump_815 =>
                    cases assump_815
                    case inl assump_844 =>
                      cases assump_844
                      case inl assump_846 =>
                        have assump_1014 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_852
                          exact assump_852
                        let assump_851 := assump_810 assump_1014
                        apply False.elim assump_851
                      case inr assump_847 =>
                        have assump_1015 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_862
                          exact assump_862
                        let assump_861 := assump_810 assump_1015
                        apply False.elim assump_861
                    case inr assump_845 =>
                      cases assump_845
                      case intro assump_868 assump_869 =>
                        have assump_1016 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                          apply Or.inr
                          intro assump_877
                          exact assump_877
                        let assump_876 := assump_810 assump_1016
                        apply False.elim assump_876
              case inr assump_807 =>
                cases assump_807
                case intro assump_883 assump_884 =>
                  cases assump_3
                  case intro assump_889 assump_890 =>
                    cases assump_890
                    case inl assump_893 =>
                      cases assump_893
                      case intro assump_895 assump_896 =>
                        cases assump_896
                        case inl assump_899 =>
                          have assump_1017 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_906
                            exact assump_906
                          let assump_905 := assump_889 assump_1017
                          apply False.elim assump_905
                        case inr assump_900 =>
                          have assump_1018 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_917
                            exact assump_917
                          let assump_916 := assump_889 assump_1018
                          apply False.elim assump_916
                    case inr assump_894 =>
                      cases assump_894
                      case inl assump_923 =>
                        cases assump_923
                        case inl assump_925 =>
                          have assump_1019 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_931
                            exact assump_931
                          let assump_930 := assump_889 assump_1019
                          apply False.elim assump_930
                        case inr assump_926 =>
                          have assump_1020 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_941
                            exact assump_941
                          let assump_940 := assump_889 assump_1020
                          apply False.elim assump_940
                      case inr assump_924 =>
                        cases assump_924
                        case intro assump_947 assump_948 =>
                          have assump_1021 : ((p6 ∧ p7) ∨ (p4 → p4)) := by
                            apply Or.inr
                            intro assump_956
                            exact assump_956
                          let assump_955 := assump_889 assump_1021
                          apply False.elim assump_955


variable (p0 p3 p1 p7 p6 p2 : Prop)
theorem file10_35238 : (((((True → p1) → False) → False) ∧ (((True → p2) ∨ (p3 → False)) ∧ ((p0 ∧ p2) ∧ (p6 ∧ p0)))) → ((((p6 → False) ∨ (p2 → False)) → False) → (((p1 ∨ p7) ∨ (p1 → p1)) ∨ ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_16
            case intro assump_23 assump_24 =>
              apply Or.inl
              apply Or.inr
              intro assump_29
              exact assump_29
      case inr assump_12 =>
        cases assump_10
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            cases assump_35
            case intro assump_42 assump_43 =>
              apply Or.inl
              apply Or.inr
              intro assump_48
              exact assump_48


variable (p4 p0 p1 p3 p7 p5 p2 : Prop)
theorem file10_36365 : ((((((p4 → False) → False) → ((False ∨ True) ∨ (p0 ∨ p2))) → False) ∧ ((((p2 ∧ p3) ∨ (True → p5)) ∨ ((False ∧ p1) → False)) ∨ (((p0 ∧ p3) ∨ (p7 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_54 : (((p4 → False) → False) → ((False ∨ True) ∨ (p0 ∨ p2))) := by
              intro assump_21
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_20 := assump_2 assump_54
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_55 : (((p4 → False) → False) → ((False ∨ True) ∨ (p0 ∨ p2))) := by
            intro assump_32
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_31 := assump_2 assump_55
          apply False.elim assump_31
      case inr assump_9 =>
        have assump_56 : (((p4 → False) → False) → ((False ∨ True) ∨ (p0 ∨ p2))) := by
          intro assump_42
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_41 := assump_2 assump_56
        apply False.elim assump_41
    case inr assump_7 =>
      have assump_57 : ((p0 ∧ p3) ∨ (p7 ∨ True)) := by
        apply Or.inr
        apply Or.inr
        apply True.intro
      let assump_50 := assump_7 assump_57
      apply False.elim assump_50


variable (p7 p0 p2 p4 : Prop)
theorem file10_37997 : ((((((p7 → p0) → (False → False)) → False) → (((p4 → p0) → (p4 → False)) ∨ ((p7 → p2) ∧ (p2 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p7 → p0) → (False → False)) → False) → (((p4 → p0) → (p4 → False)) ∨ ((p7 → p2) ∧ (p2 ∨ p7)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_29 : ((p7 → p0) → (False → False)) := by
      intro assump_18
      intro assump_19
      apply False.elim assump_19
    let assump_17 := assump_5 assump_29
    apply False.elim assump_17
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p7 p6 p1 p0 p4 p2 p3 : Prop)
theorem file10_38670 : (((((p6 ∧ p0) → (p7 ∧ False)) ∧ ((p1 ∨ p6) ∨ (p3 ∨ p6))) ∧ (((p4 → False) ∨ (p1 ∨ p6)) ∧ ((p0 ∨ True) → False))) → ((((False → False) ∨ (p4 → p2)) → ((p0 → p1) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_6
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              have assump_145 : (p0 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_25 := assump_18 assump_145
              apply False.elim assump_25
            case inr assump_20 =>
              cases assump_20
              case inl assump_29 =>
                have assump_146 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_35 := assump_18 assump_146
                apply False.elim assump_35
              case inr assump_30 =>
                have assump_147 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_43 := assump_18 assump_147
                apply False.elim assump_43
        case inr assump_14 =>
          cases assump_6
          case intro assump_49 assump_50 =>
            cases assump_49
            case inl assump_51 =>
              have assump_148 : (p0 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_57 := assump_50 assump_148
              apply False.elim assump_57
            case inr assump_52 =>
              cases assump_52
              case inl assump_61 =>
                have assump_149 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_67 := assump_50 assump_149
                apply False.elim assump_67
              case inr assump_62 =>
                have assump_150 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_75 := assump_50 assump_150
                apply False.elim assump_75
      case inr assump_12 =>
        cases assump_12
        case inl assump_79 =>
          cases assump_6
          case intro assump_83 assump_84 =>
            cases assump_83
            case inl assump_85 =>
              have assump_151 : (p0 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_91 := assump_84 assump_151
              apply False.elim assump_91
            case inr assump_86 =>
              cases assump_86
              case inl assump_95 =>
                have assump_152 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_101 := assump_84 assump_152
                apply False.elim assump_101
              case inr assump_96 =>
                have assump_153 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_109 := assump_84 assump_153
                apply False.elim assump_109
        case inr assump_80 =>
          cases assump_6
          case intro assump_115 assump_116 =>
            cases assump_115
            case inl assump_117 =>
              have assump_154 : (p0 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_123 := assump_116 assump_154
              apply False.elim assump_123
            case inr assump_118 =>
              cases assump_118
              case inl assump_127 =>
                have assump_155 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_133 := assump_116 assump_155
                apply False.elim assump_133
              case inr assump_128 =>
                have assump_156 : (p0 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_141 := assump_116 assump_156
                apply False.elim assump_141


variable (p0 p5 p6 p7 p2 p1 p4 : Prop)
theorem file10_42933 : (((((True ∨ p4) → False) ∨ ((True → p2) ∧ (p7 → False))) → (((p0 → False) → (False → p4)) ∨ ((False ∧ p6) ∧ (p0 → False)))) ∨ ((((True → False) → False) → ((p6 ∧ p1) → (p2 ∧ p4))) ∧ (((True → p0) → (p5 → True)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case intro assump_10 assump_11 =>
      apply Or.inl
      intro assump_16
      intro assump_17
      apply False.elim assump_17


variable (p2 p3 p1 p5 p6 p0 p4 p7 : Prop)
theorem file10_43560 : ((((((p5 ∧ p5) ∨ (True ∨ p6)) ∧ ((p2 → False) ∧ (p7 → p1))) → (((False → False) → False) ∧ ((p3 ∧ True) → False))) ∧ ((((True → True) → False) ∧ ((p3 → p4) ∨ (p3 → p5))) ∧ (((p5 → True) ∧ (False → p3)) ∨ ((p6 ∨ p1) → (p0 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_7
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_68 : (True → True) := by
                intro assump_28
                apply True.intro
              let assump_27 := assump_8 assump_68
              apply False.elim assump_27
          case inr assump_17 =>
            have assump_69 : (True → True) := by
              intro assump_37
              apply True.intro
            let assump_36 := assump_8 assump_69
            apply False.elim assump_36
        case inr assump_13 =>
          cases assump_7
          case inl assump_43 =>
            cases assump_43
            case intro assump_45 assump_46 =>
              have assump_70 : (True → True) := by
                intro assump_55
                apply True.intro
              let assump_54 := assump_8 assump_70
              apply False.elim assump_54
          case inr assump_44 =>
            have assump_71 : (True → True) := by
              intro assump_64
              apply True.intro
            let assump_63 := assump_8 assump_71
            apply False.elim assump_63


variable (p6 p1 p0 p4 p3 p2 p7 : Prop)
theorem file10_45271 : ((((((p2 → False) → (p4 ∨ p6)) ∨ ((True → p2) → (True ∧ p0))) → False) ∧ ((((False ∧ p3) → False) ∨ ((p7 ∨ p1) → False)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_21 : (((False ∧ p3) → False) ∨ ((p7 ∨ p1) → False)) := by
      apply Or.inl
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_12 := assump_7 assump_21
    apply False.elim assump_12


variable (p5 p2 p3 p7 p1 p4 : Prop)
theorem file10_45828 : (((((False ∨ False) → (True ∨ p1)) ∨ ((p7 ∨ p1) → (p4 → False))) → (((p4 → p2) → False) → ((p2 ∨ p5) ∨ (p4 → p4)))) ∨ ((((p1 → p3) → (True ∧ p1)) ∨ ((p3 → p2) ∧ (p4 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inr
    intro assump_9
    exact assump_9
  case inr assump_6 =>
    apply Or.inr
    intro assump_14
    exact assump_14


variable (p5 p2 p4 p7 p0 p6 : Prop)
theorem file10_46304 : (((((True ∧ p6) ∨ (False → p6)) ∧ ((False → True) ∨ (p5 → p4))) → False) → ((((p7 ∨ p0) ∨ (False ∨ True)) ∧ ((p2 → False) → (p7 ∨ p4))) ∧ (((p2 → False) ∨ (p7 → False)) ∨ ((p6 → False) → (p6 ∨ p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inr
  apply Or.inr
  apply True.intro
  intro assump_4
  have assump_31 : (((True ∧ p6) ∨ (False → p6)) ∧ ((False → True) ∨ (p5 → p4))) := by
    apply And.intro
    apply Or.inr
    intro assump_10
    apply False.elim assump_10
    apply Or.inl
    intro assump_13
    apply True.intro
  let assump_9 := assump_1 assump_31
  apply False.elim assump_9
  apply Or.inl
  apply Or.inl
  intro assump_19
  have assump_32 : (((True ∧ p6) ∨ (False → p6)) ∧ ((False → True) ∨ (p5 → p4))) := by
    apply And.intro
    apply Or.inr
    intro assump_24
    apply False.elim assump_24
    apply Or.inl
    intro assump_27
    apply True.intro
  let assump_23 := assump_1 assump_32
  apply False.elim assump_23


variable (p4 p0 p2 p5 p7 p3 p6 : Prop)
theorem file10_47339 : (((((p2 ∧ p4) ∨ (p6 ∧ p5)) → False) ∧ (((p7 ∧ p0) → False) ∨ ((p2 ∧ p4) ∧ (p2 ∧ p3)))) → ((((False ∧ False) → False) → False) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    cases assump_14
    case inl assump_17 =>
      have assump_54 : ((False ∧ False) → False) := by
        intro assump_24
        cases assump_24
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
      let assump_23 := assump_10 assump_54
      apply False.elim assump_23
    case inr assump_18 =>
      cases assump_18
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          cases assump_33
          case intro assump_40 assump_41 =>
            have assump_55 : ((p2 ∧ p4) ∨ (p6 ∧ p5)) := by
              apply Or.inl
              apply And.intro
              exact assump_40
              exact assump_35
            let assump_50 := assump_13 assump_55
            apply False.elim assump_50


variable (p4 p3 p7 p0 p6 p2 p1 p5 : Prop)
theorem file10_48427 : (((((p7 → p4) → (p7 ∧ p4)) ∧ ((p7 ∧ p0) → (p1 → False))) → (((p7 → False) ∧ (p5 ∧ p3)) ∨ ((p5 ∨ p0) ∨ (p0 → p1)))) → ((((p0 ∧ p7) ∨ (p6 → False)) → ((False → False) ∨ (p2 → p6))) ∨ (((p7 ∧ p6) → (p6 ∨ True)) → ((p2 ∧ p6) ∨ (True → True))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
  case inr assump_6 =>
    apply Or.inl
    intro assump_18
    apply False.elim assump_18


variable (p3 p1 p7 : Prop)
theorem file10_49034 : (((((p7 → p3) ∧ (False ∧ p7)) → ((False ∨ p3) → (p3 ∧ p1))) → False) → False) := by
  intro assump_1
  have assump_38 : (((p7 → p3) ∧ (False ∧ p7)) → ((False ∨ p3) → (p3 ∧ p1))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      apply False.elim assump_7
    case inr assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
    cases assump_6
    case inl assump_21 =>
      apply False.elim assump_21
    case inr assump_22 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_28
        case intro assump_31 assump_32 =>
          apply False.elim assump_31
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p3 p0 p2 p1 p6 p4 : Prop)
theorem file10_49934 : (((((p3 → False) → (p3 → False)) → False) → (((p2 ∨ p6) → (p2 ∨ p6)) ∧ ((p2 ∧ True) → False))) ∨ ((((p0 ∨ p2) → False) ∧ ((p1 ∨ False) → False)) ∨ (((p1 → False) ∨ (p0 → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    exact assump_3
  case inr assump_4 =>
    apply Or.inr
    exact assump_4
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    have assump_36 : ((p3 → False) → (p3 → False)) := by
      intro assump_23
      intro assump_24
      have assump_37 : p3 := by
        exact assump_24
      let assump_29 := assump_23 assump_37
      apply False.elim assump_29
    let assump_22 := assump_1 assump_36
    apply False.elim assump_22


variable (p3 p7 p4 p2 : Prop)
theorem file10_50758 : ((((((True → False) → (p2 ∧ p7)) ∨ ((False → False) → False)) ∨ (((p3 → False) ∧ (p3 → False)) ∨ ((p4 → False) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((True → False) → (p2 ∧ p7)) ∨ ((False → False) → False)) ∨ (((p3 → False) ∧ (p3 → False)) ∨ ((p4 → False) ∧ (False → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply And.intro
    have assump_22 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
    have assump_23 : True := by
      apply True.intro
    let assump_14 := assump_5 assump_23
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p3 p1 p5 p6 : Prop)
theorem file10_51531 : ((((((False ∨ p5) ∧ (p4 → p6)) → ((p5 ∧ p6) ∧ (False → True))) → (((False ∧ p5) ∧ (p1 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∨ p5) ∧ (p4 → p6)) → ((p5 ∧ p6) ∧ (False → True))) → (((False ∧ p5) ∧ (p1 → p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p4 p7 p5 p3 p6 : Prop)
theorem file10_52113 : ((((((False → False) → False) ∧ ((True ∨ p3) ∨ (p4 ∧ p5))) → (((p7 → True) ∨ (p6 → False)) ∨ ((p4 → False) → (p2 → False)))) → False) → False) := by
  intro assump_11
  have assump_40 : ((((False → False) → False) ∧ ((True ∨ p3) ∨ (p4 ∧ p5))) → (((p7 → True) ∨ (p6 → False)) ∨ ((p4 → False) → (p2 → False)))) := by
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      cases assump_17
      case inl assump_20 =>
        cases assump_20
        case inl assump_22 =>
          apply Or.inl
          apply Or.inl
          intro assump_26
          apply True.intro
        case inr assump_23 =>
          apply Or.inl
          apply Or.inl
          intro assump_29
          apply True.intro
      case inr assump_21 =>
        cases assump_21
        case intro assump_30 assump_31 =>
          apply Or.inl
          apply Or.inl
          intro assump_36
          apply True.intro
  let assump_14 := assump_11 assump_40
  apply False.elim assump_14


variable (p6 p1 p5 p2 p7 p0 : Prop)
theorem file10_53159 : (((((p2 → False) ∧ (False ∧ p7)) ∧ ((p0 → p5) ∧ (p2 → False))) → False) ∨ ((((p1 → p5) ∨ (p6 → True)) → False) ∧ (((p7 ∨ p2) → False) ∧ ((p7 ∧ p1) ∨ (True → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply False.elim assump_8


variable (p4 p5 p2 p3 p0 p6 p7 p1 : Prop)
theorem file10_53630 : ((((((p5 ∨ False) → (p0 ∨ p4)) → ((p5 ∨ p6) ∨ (True ∨ p7))) ∨ (((p3 ∨ p6) → (False → p1)) → ((p0 → False) → (True → p2)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 ∨ False) → (p0 ∨ p4)) → ((p5 ∨ p6) ∨ (True ∨ p7))) ∨ (((p3 ∨ p6) → (False → p1)) → ((p0 → False) → (True → p2)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p5 p6 p7 p1 p4 p2 : Prop)
theorem file10_54159 : ((((((False ∨ p6) → (p4 ∧ p2)) → ((p2 ∨ False) ∨ (False → p1))) ∨ (((p4 → p1) → (True ∨ p1)) ∨ ((p0 ∨ True) → (p7 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((False ∨ p6) → (p4 ∧ p2)) → ((p2 ∨ False) ∨ (False → p1))) ∨ (((p4 → p1) → (True ∨ p1)) ∨ ((p0 ∨ True) → (p7 ∧ p5)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p7 p6 p1 p3 p4 : Prop)
theorem file10_54696 : (((((True → False) → (p2 → False)) → ((False ∧ p7) ∨ (True ∨ False))) → False) → ((((True ∧ p1) ∨ (p7 → False)) ∨ ((p3 → p6) → (True → p1))) ∧ (((False → p4) → False) ∧ ((p1 ∨ p3) → (p1 → False))))) := by
  intro assump_5
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_8
  have assump_59 : (((True → False) → (p2 → False)) → ((False ∧ p7) ∨ (True ∨ False))) := by
    intro assump_13
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_12 := assump_5 assump_59
  apply False.elim assump_12
  apply And.intro
  intro assump_19
  have assump_60 : (((True → False) → (p2 → False)) → ((False ∧ p7) ∨ (True ∨ False))) := by
    intro assump_25
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_24 := assump_5 assump_60
  apply False.elim assump_24
  intro assump_31
  intro assump_32
  cases assump_31
  case inl assump_35 =>
    have assump_61 : (((True → False) → (p2 → False)) → ((False ∧ p7) ∨ (True ∨ False))) := by
      intro assump_42
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_41 := assump_5 assump_61
    apply False.elim assump_41
  case inr assump_36 =>
    have assump_62 : (((True → False) → (p2 → False)) → ((False ∧ p7) ∨ (True ∨ False))) := by
      intro assump_53
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_52 := assump_5 assump_62
    apply False.elim assump_52


variable (p2 p0 p3 p6 : Prop)
theorem file10_56143 : (((((True → False) → (p2 ∨ p2)) → False) → False) ∨ ((((p3 ∨ p0) ∧ (p3 → False)) → ((False → False) → False)) ∧ (((p0 ∧ p0) ∧ (False → p6)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((True → False) → (p2 ∨ p2)) := by
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p1 p0 p2 p4 : Prop)
theorem file10_56651 : (((((False ∧ p4) → False) ∨ ((p4 → True) → (p1 → p2))) ∨ (((p3 → p1) → False) → False)) ∨ ((((False ∧ False) ∧ (p4 → False)) ∧ ((p4 ∧ p2) → (p2 ∧ p3))) ∧ (((p3 → True) ∧ (p0 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p5 p3 p7 p2 p0 p6 : Prop)
theorem file10_57055 : ((((((True → False) → (p6 ∧ p0)) → ((p0 → p2) ∧ (p5 ∨ p2))) ∧ (((p6 → p0) → False) → False)) ∧ ((((p3 → p6) ∨ (p7 → p7)) → False) ∧ (((p5 ∧ p2) → (False ∧ p6)) ∧ ((False ∧ p6) ∧ (p5 → p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_20


variable (p1 p0 p2 p3 : Prop)
theorem file10_57751 : (((((p3 ∧ p1) → False) → ((False → p2) ∨ (p0 ∨ p0))) → (((True → False) → (p1 → p2)) → False)) → False) := by
  intro assump_1
  have assump_25 : (((p3 ∧ p1) → False) → ((False → p2) ∨ (p0 ∨ p0))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  have assump_26 : ((True → False) → (p1 → p2)) := by
    intro assump_12
    intro assump_13
    have assump_27 : True := by
      apply True.intro
    let assump_18 := assump_12 assump_27
    apply False.elim assump_18
  let assump_11 := assump_4 assump_26
  apply False.elim assump_11


variable (p1 p5 p0 : Prop)
theorem file10_58415 : ((((((p5 → True) → False) ∨ ((p1 → False) ∧ (False ∧ p0))) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p5 → True) → False) ∨ ((p1 → False) ∧ (False ∧ p0))) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      have assump_27 : (p5 → True) := by
        intro assump_11
        apply True.intro
      let assump_10 := assump_6 assump_27
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p7 p5 p6 p4 p3 : Prop)
theorem file10_59157 : ((((((p1 → False) ∨ (p4 ∧ p7)) ∧ ((p6 → p4) → False)) → (((False ∧ p3) ∨ (False → p4)) ∧ ((p5 ∧ p3) → (False → p6)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p1 → False) ∨ (p4 ∧ p7)) ∧ ((p6 → p4) → False)) → (((False ∧ p3) ∨ (False → p4)) ∧ ((p5 ∧ p3) → (False → p6)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        intro assump_14
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_17 assump_18 =>
          apply Or.inr
          intro assump_25
          apply False.elim assump_25
    intro assump_28
    intro assump_29
    apply False.elim assump_29
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p5 p2 p0 p7 p1 p6 p3 p4 : Prop)
theorem file10_60059 : (((((p0 ∨ p0) → (p3 → p1)) ∧ ((p3 → p7) ∧ (p1 ∧ p5))) → False) → ((((p6 → False) → (p4 → p4)) ∨ ((p6 → p5) ∨ (p6 ∧ p2))) ∨ (((p4 → False) → (p2 ∧ True)) ∨ ((p6 ∧ p7) → (p3 ∧ True))))) := by
  intro assump_15
  apply Or.inl
  apply Or.inl
  intro assump_18
  intro assump_19
  exact assump_19


variable (p7 p2 p6 p3 p5 p1 : Prop)
theorem file10_60411 : (((((False → p7) ∧ (False → False)) → False) ∨ (((p1 → False) → (p1 ∨ p6)) ∧ ((p6 ∨ True) → False))) → ((((p5 ∧ p2) → False) ∨ ((p5 → False) ∨ (p3 → p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      have assump_85 : ((False → p7) ∧ (False → False)) := by
        apply And.intro
        intro assump_12
        apply False.elim assump_12
        intro assump_15
        apply False.elim assump_15
      let assump_11 := assump_7 assump_85
      apply False.elim assump_11
    case inr assump_8 =>
      cases assump_8
      case intro assump_21 assump_22 =>
        have assump_86 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_27 := assump_22 assump_86
        apply False.elim assump_27
  case inr assump_4 =>
    cases assump_4
    case inl assump_31 =>
      cases assump_1
      case inl assump_35 =>
        have assump_87 : ((False → p7) ∧ (False → False)) := by
          apply And.intro
          intro assump_40
          apply False.elim assump_40
          intro assump_43
          apply False.elim assump_43
        let assump_39 := assump_35 assump_87
        apply False.elim assump_39
      case inr assump_36 =>
        cases assump_36
        case intro assump_49 assump_50 =>
          have assump_88 : (p6 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_55 := assump_50 assump_88
          apply False.elim assump_55
    case inr assump_32 =>
      cases assump_1
      case inl assump_61 =>
        have assump_89 : ((False → p7) ∧ (False → False)) := by
          apply And.intro
          intro assump_66
          apply False.elim assump_66
          intro assump_69
          apply False.elim assump_69
        let assump_65 := assump_61 assump_89
        apply False.elim assump_65
      case inr assump_62 =>
        cases assump_62
        case intro assump_75 assump_76 =>
          have assump_90 : (p6 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_81 := assump_76 assump_90
          apply False.elim assump_81


variable (p6 p4 p7 : Prop)
theorem file10_62627 : (((((p6 → True) → False) → False) ∨ (((p4 → False) ∨ (True → p7)) → False)) ∧ ((((False ∧ p6) → False) → False) → False)) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_21 : (p6 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4
  intro assump_9
  have assump_22 : ((False ∧ p6) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
  let assump_12 := assump_9 assump_22
  apply False.elim assump_12


variable (p1 p4 p5 p3 p0 p6 p7 p2 : Prop)
theorem file10_63256 : (((((True ∧ True) ∨ (p0 ∧ True)) → ((p1 ∨ p7) ∨ (p0 ∨ False))) → (((p5 ∨ p5) ∧ (p2 → False)) ∨ ((p6 → False) ∧ (p3 ∧ p1)))) → ((((p0 ∧ p3) ∨ (False → False)) → ((p6 ∧ True) ∧ (p1 ∧ p4))) → (((p1 → p6) ∧ (p1 ∧ False)) → ((True → p2) ∨ (p2 ∧ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      apply False.elim assump_9


variable (p3 p5 p7 p0 p4 p1 p6 p2 : Prop)
theorem file10_63765 : (((((p4 → False) → False) → ((p5 ∧ False) → False)) ∨ (((p7 ∧ True) ∨ (p0 ∨ p5)) ∨ ((False ∨ p3) → (False → p6)))) ∨ ((((p7 ∧ True) ∧ (p1 → False)) ∧ ((p4 → False) ∨ (p3 → p3))) ∧ (((p1 ∧ p1) → False) → ((p3 → False) ∧ (p2 → p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p0 p3 p6 p4 p5 p7 : Prop)
theorem file10_64209 : ((((((p5 ∧ p5) ∧ (p4 → p4)) → ((p6 → False) → (p4 → p6))) ∧ (((p4 ∨ False) ∨ (True ∨ p3)) → ((p7 → False) → (p6 ∨ p0)))) ∧ ((((p0 → p7) → False) → ((True ∧ p4) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_21 : (((p0 → p7) → False) → ((True ∧ p4) → (False → False))) := by
        intro assump_13
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      let assump_12 := assump_3 assump_21
      apply False.elim assump_12


variable (p2 p3 p4 p6 p0 p1 p7 : Prop)
theorem file10_64867 : (((((p6 → False) ∨ (p6 ∧ p4)) ∧ ((p2 ∧ p4) → (p4 ∧ p4))) → (((p3 → p1) → (p7 ∨ p4)) → ((p2 ∨ p7) → False))) → ((((False → p0) → False) → False) ∨ (((p4 → False) ∧ (p4 → False)) ∨ ((False ∨ True) → (p4 ∨ p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (False → p0) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p4 p1 p3 p7 p5 p6 p0 : Prop)
theorem file10_65348 : (((((p1 ∧ p5) → False) → False) ∧ (((p3 → False) ∧ (p1 ∨ p1)) ∨ ((p1 ∧ p4) ∧ (p0 ∨ False)))) → ((((p3 → False) → False) ∨ ((p3 → False) ∧ (p5 ∨ p6))) → (((True ∨ p0) ∨ (p7 ∧ p4)) ∧ ((p0 → p1) ∧ (False → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_14
          case inl assump_17 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_18 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      case inr assump_12 =>
        cases assump_12
        case intro assump_23 assump_24 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            cases assump_24
            case inl assump_31 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_32 =>
              apply False.elim assump_32
  case inr assump_4 =>
    cases assump_4
    case intro assump_37 assump_38 =>
      cases assump_38
      case inl assump_41 =>
        cases assump_1
        case intro assump_45 assump_46 =>
          cases assump_46
          case inl assump_49 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              cases assump_52
              case inl assump_55 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_56 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_50 =>
            cases assump_50
            case intro assump_61 assump_62 =>
              cases assump_61
              case intro assump_63 assump_64 =>
                cases assump_62
                case inl assump_69 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_70 =>
                  apply False.elim assump_70
      case inr assump_42 =>
        cases assump_1
        case intro assump_77 assump_78 =>
          cases assump_78
          case inl assump_81 =>
            cases assump_81
            case intro assump_83 assump_84 =>
              cases assump_84
              case inl assump_87 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_88 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_82 =>
            cases assump_82
            case intro assump_93 assump_94 =>
              cases assump_93
              case intro assump_95 assump_96 =>
                cases assump_94
                case inl assump_101 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_102 =>
                  apply False.elim assump_102
  apply And.intro
  intro assump_107
  cases assump_2
  case inl assump_110 =>
    cases assump_1
    case intro assump_114 assump_115 =>
      cases assump_115
      case inl assump_118 =>
        cases assump_118
        case intro assump_120 assump_121 =>
          cases assump_121
          case inl assump_124 =>
            exact assump_124
          case inr assump_125 =>
            exact assump_125
      case inr assump_119 =>
        cases assump_119
        case intro assump_130 assump_131 =>
          cases assump_130
          case intro assump_132 assump_133 =>
            cases assump_131
            case inl assump_138 =>
              exact assump_132
            case inr assump_139 =>
              apply False.elim assump_139
  case inr assump_111 =>
    cases assump_111
    case intro assump_144 assump_145 =>
      cases assump_145
      case inl assump_148 =>
        cases assump_1
        case intro assump_152 assump_153 =>
          cases assump_153
          case inl assump_156 =>
            cases assump_156
            case intro assump_158 assump_159 =>
              cases assump_159
              case inl assump_162 =>
                exact assump_162
              case inr assump_163 =>
                exact assump_163
          case inr assump_157 =>
            cases assump_157
            case intro assump_168 assump_169 =>
              cases assump_168
              case intro assump_170 assump_171 =>
                cases assump_169
                case inl assump_176 =>
                  exact assump_170
                case inr assump_177 =>
                  apply False.elim assump_177
      case inr assump_149 =>
        cases assump_1
        case intro assump_184 assump_185 =>
          cases assump_185
          case inl assump_188 =>
            cases assump_188
            case intro assump_190 assump_191 =>
              cases assump_191
              case inl assump_194 =>
                exact assump_194
              case inr assump_195 =>
                exact assump_195
          case inr assump_189 =>
            cases assump_189
            case intro assump_200 assump_201 =>
              cases assump_200
              case intro assump_202 assump_203 =>
                cases assump_201
                case inl assump_208 =>
                  exact assump_202
                case inr assump_209 =>
                  apply False.elim assump_209
  intro assump_214
  apply False.elim assump_214


variable (p6 p7 p5 p3 p1 p4 p0 p2 : Prop)
theorem file10_71006 : ((((((p2 ∧ False) → (p7 → True)) → ((p5 ∨ True) → (p3 → p3))) ∨ (((p5 ∧ p1) ∨ (p6 ∧ p4)) ∨ ((p4 ∨ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p2 ∧ False) → (p7 → True)) → ((p5 ∨ True) → (p3 → p3))) ∨ (((p5 ∧ p1) ∨ (p6 ∧ p4)) ∨ ((p4 ∨ p0) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      exact assump_7
    case inr assump_11 =>
      exact assump_7
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p5 p6 p0 p2 p3 p7 : Prop)
theorem file10_71611 : ((((((p4 ∧ p6) → (p5 ∧ p2)) → False) → False) ∧ ((((p7 → True) ∨ (p6 ∧ p6)) ∨ ((p7 ∨ p5) ∨ (p0 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p7 → True) ∨ (p6 ∧ p6)) ∨ ((p7 ∨ p5) ∨ (p0 ∨ p3))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p0 p6 p2 p1 p4 p7 p5 : Prop)
theorem file10_72102 : (((((p1 → False) ∧ (True → False)) → ((p1 ∨ False) → False)) ∧ (((p0 ∨ p5) ∨ (p0 → p2)) → False)) → ((((p0 → p4) → (p0 → False)) ∨ ((p2 → False) ∧ (p5 ∨ p6))) ∨ (((True ∧ True) ∨ (p6 ∧ p4)) → ((p1 ∨ p7) ∧ (p2 ∧ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_21 : ((p0 ∨ p5) ∨ (p0 → p2)) := by
      apply Or.inl
      apply Or.inl
      exact assump_9
    let assump_17 := assump_3 assump_21
    apply False.elim assump_17


variable (p2 p6 p7 p4 p1 p0 p5 : Prop)
theorem file10_72711 : (((((p6 ∨ p0) → (p7 → False)) ∨ ((p1 → p5) ∧ (False → False))) → (((p1 → False) ∨ (p4 ∧ p4)) → ((False → p1) ∧ (False ∨ True)))) ∨ ((((p7 ∨ p0) ∧ (p4 → False)) → ((p7 → False) ∨ (p7 → p7))) ∧ (((p6 ∨ p2) ∧ (False ∧ p6)) ∨ ((p4 → p6) → (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case inl assump_10 =>
      apply Or.inr
      apply True.intro
    case inr assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply Or.inr
        apply True.intro
  case inr assump_7 =>
    cases assump_7
    case intro assump_20 assump_21 =>
      cases assump_1
      case inl assump_26 =>
        apply Or.inr
        apply True.intro
      case inr assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          apply Or.inr
          apply True.intro


variable (p0 p2 p5 p4 p1 p7 : Prop)
theorem file10_73721 : ((((((True → False) → False) ∨ ((p7 ∧ True) → (p7 → p0))) ∨ (((p5 ∨ p4) → (p5 ∧ False)) ∧ ((p1 ∧ p2) ∨ (p1 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True → False) → False) ∨ ((p7 ∧ True) → (p7 → p0))) ∨ (((p5 ∨ p4) → (p5 ∧ False)) ∧ ((p1 ∧ p2) ∨ (p1 ∨ True)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p3 p0 p1 : Prop)
theorem file10_74317 : (((((p1 ∧ p3) → (p0 → p3)) ∨ ((p6 → p6) ∨ (True → True))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p1 ∧ p3) → (p0 → p3)) ∨ ((p6 → p6) ∨ (True → True))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p7 p6 p1 p2 p5 p4 p3 : Prop)
theorem file10_74761 : (((((p1 ∨ p0) ∨ (p7 ∨ p4)) ∨ ((False ∨ p3) → False)) → (((p3 ∨ p4) ∨ (False ∨ p6)) ∨ ((p7 → False) → (True ∨ True)))) ∨ ((((p0 ∨ p5) → False) → False) ∨ (((p2 ∨ p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inr
        intro assump_10
        apply Or.inl
        apply True.intro
      case inr assump_7 =>
        apply Or.inr
        intro assump_15
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      cases assump_5
      case inl assump_18 =>
        apply Or.inr
        intro assump_22
        apply Or.inl
        apply True.intro
      case inr assump_19 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        exact assump_19
  case inr assump_3 =>
    apply Or.inr
    intro assump_29
    apply Or.inl
    apply True.intro


variable (p4 p2 p1 p0 p5 p6 p7 : Prop)
theorem file10_75766 : ((((((p7 ∨ p5) ∨ (p2 ∨ True)) ∧ ((p5 → False) → (p6 ∨ p2))) ∧ (((p5 ∨ False) → False) ∧ ((p7 → False) ∧ (p1 ∧ False)))) ∧ ((((p0 ∨ p6) → False) ∨ ((p5 → p4) ∨ (p0 → False))) → (((False ∧ p6) ∧ (p2 → False)) → ((p0 → p0) → (True ∧ False))))) → False) := by
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
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
          case inr assump_11 =>
            cases assump_5
            case intro assump_34 assump_35 =>
              cases assump_35
              case intro assump_38 assump_39 =>
                cases assump_39
                case intro assump_42 assump_43 =>
                  apply False.elim assump_43
        case inr assump_9 =>
          cases assump_9
          case inl assump_48 =>
            cases assump_5
            case intro assump_54 assump_55 =>
              cases assump_55
              case intro assump_58 assump_59 =>
                cases assump_59
                case intro assump_62 assump_63 =>
                  apply False.elim assump_63
          case inr assump_49 =>
            cases assump_5
            case intro assump_72 assump_73 =>
              cases assump_73
              case intro assump_76 assump_77 =>
                cases assump_77
                case intro assump_80 assump_81 =>
                  apply False.elim assump_81


variable (p0 p6 p4 : Prop)
theorem file10_77626 : (((((p0 → p0) → False) → ((p4 → p0) → (False ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_32 : (((p0 → p0) → False) → ((p4 → p0) → (False ∧ p6))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    have assump_33 : (p0 → p0) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_5 assump_33
    apply False.elim assump_11
    have assump_34 : (p0 → p0) := by
      intro assump_23
      exact assump_23
    let assump_22 := assump_5 assump_34
    apply False.elim assump_22
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p2 p5 p4 p7 p0 p3 p1 p6 : Prop)
theorem file10_78289 : ((((((p0 ∧ p3) → False) → ((p2 ∧ p2) → (p6 → False))) ∨ (((p2 → False) → False) → ((p5 → p3) → False))) ∧ ((((p1 ∨ p3) → (p7 ∨ p1)) → ((p6 ∨ False) → (p4 ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_42 : (((p1 ∨ p3) → (p7 ∨ p1)) → ((p6 ∨ False) → (p4 ∨ True))) := by
        intro assump_11
        intro assump_12
        cases assump_12
        case inl assump_13 =>
          apply Or.inr
          apply True.intro
        case inr assump_14 =>
          apply False.elim assump_14
      let assump_10 := assump_3 assump_42
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_43 : (((p1 ∨ p3) → (p7 ∨ p1)) → ((p6 ∨ False) → (p4 ∨ True))) := by
        intro assump_29
        intro assump_30
        cases assump_30
        case inl assump_31 =>
          apply Or.inr
          apply True.intro
        case inr assump_32 =>
          apply False.elim assump_32
      let assump_28 := assump_3 assump_43
      apply False.elim assump_28


variable (p2 p3 p0 p7 p1 p5 : Prop)
theorem file10_79435 : (((((True ∧ True) ∨ (p2 → False)) → False) ∧ (((p3 ∨ p0) ∧ (p1 → p5)) ∧ ((p3 → p7) ∨ (True → p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case inl assump_16 =>
            have assump_63 : ((True ∧ True) ∨ (p2 → False)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_24 := assump_2 assump_63
            apply False.elim assump_24
          case inr assump_17 =>
            have assump_64 : ((True ∧ True) ∨ (p2 → False)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_34 := assump_2 assump_64
            apply False.elim assump_34
        case inr assump_11 =>
          cases assump_7
          case inl assump_42 =>
            have assump_65 : ((True ∧ True) ∨ (p2 → False)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_49 := assump_2 assump_65
            apply False.elim assump_49
          case inr assump_43 =>
            have assump_66 : ((True ∧ True) ∨ (p2 → False)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_59 := assump_2 assump_66
            apply False.elim assump_59


variable (p6 p0 p2 p1 p4 : Prop)
theorem file10_81138 : ((((((p4 → p4) → (p0 → p6)) → False) → (((p0 ∧ p0) ∨ (False → False)) ∨ ((p2 → False) ∧ (p1 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p4 → p4) → (p0 → p6)) → False) → (((p0 ∧ p0) ∨ (False → False)) ∨ ((p2 → False) ∧ (p1 ∧ p1)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p7 p0 : Prop)
theorem file10_81622 : ((((((p0 → False) → (True → False)) → False) → (((p1 ∧ p0) → False) ∨ ((p0 ∨ p1) → (True ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p0 → False) → (True → False)) → False) → (((p1 ∧ p0) → False) ∨ ((p0 ∨ p1) → (True ∨ p7)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_35 : ((p0 → False) → (True → False)) := by
        intro assump_18
        intro assump_19
        have assump_36 : p0 := by
          exact assump_10
        let assump_24 := assump_18 assump_36
        apply False.elim assump_24
      let assump_17 := assump_5 assump_35
      apply False.elim assump_17
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p7 p2 p3 p4 p6 : Prop)
theorem file10_82439 : ((((((p3 → False) → False) ∧ ((p3 → False) ∧ (p6 → False))) → (((False ∨ p4) ∨ (p6 → True)) ∧ ((p2 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_77 : ((((p3 → False) → False) ∧ ((p3 → False) ∧ (p6 → False))) → (((False ∨ p4) ∨ (p6 → True)) ∧ ((p2 ∨ p7) → False))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inr
        intro assump_16
        apply True.intro
    intro assump_17
    cases assump_17
    case inl assump_18 =>
      cases assump_5
      case intro assump_22 assump_23 =>
        cases assump_23
        case intro assump_26 assump_27 =>
          have assump_78 : (p3 → False) := by
            intro assump_35
            have assump_79 : p3 := by
              exact assump_35
            let assump_40 := assump_26 assump_79
            apply False.elim assump_40
          let assump_34 := assump_22 assump_78
          apply False.elim assump_34
    case inr assump_19 =>
      cases assump_5
      case intro assump_49 assump_50 =>
        cases assump_50
        case intro assump_53 assump_54 =>
          have assump_80 : (p3 → False) := by
            intro assump_62
            have assump_81 : p3 := by
              exact assump_62
            let assump_67 := assump_53 assump_81
            apply False.elim assump_67
          let assump_61 := assump_49 assump_80
          apply False.elim assump_61
  let assump_4 := assump_1 assump_77
  apply False.elim assump_4


variable (p5 p4 p1 p3 p2 p7 p6 : Prop)
theorem file10_84062 : ((((((p5 → False) → False) ∧ ((p3 ∨ p2) → False)) → (((p4 → False) → (p1 ∧ p4)) ∨ ((p5 → False) ∧ (p1 ∨ p2)))) ∧ ((((True → False) → (p3 → False)) → False) ∧ (((p3 ∧ p6) ∨ (p2 ∧ p7)) ∧ ((p7 ∧ p5) ∧ (p2 → False))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_15
            case intro assump_24 assump_25 =>
              cases assump_24
              case intro assump_26 assump_27 =>
                have assump_73 : ((True → False) → (p3 → False)) := by
                  intro assump_40
                  intro assump_41
                  have assump_74 : True := by
                    apply True.intro
                  let assump_46 := assump_40 assump_74
                  apply False.elim assump_46
                let assump_39 := assump_10 assump_73
                apply False.elim assump_39
        case inr assump_17 =>
          cases assump_17
          case intro assump_53 assump_54 =>
            cases assump_15
            case intro assump_59 assump_60 =>
              cases assump_59
              case intro assump_61 assump_62 =>
                have assump_75 : p2 := by
                  exact assump_53
                let assump_69 := assump_60 assump_75
                apply False.elim assump_69


variable (p7 p6 p5 p1 p0 : Prop)
theorem file10_85654 : (((((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) → False) → ((((p0 ∨ p0) ∧ (p5 → p1)) → ((p7 ∨ p1) → False)) ∧ (((p6 ∨ p0) ∨ (p5 → p1)) → False))) := by
  intro assump_9
  apply And.intro
  intro assump_10
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    cases assump_10
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        have assump_144 : (((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) := by
          apply Or.inr
          intro assump_27
          have assump_145 : True := by
            apply True.intro
          let assump_30 := assump_27 assump_145
          apply False.elim assump_30
        let assump_26 := assump_9 assump_144
        apply False.elim assump_26
      case inr assump_19 =>
        have assump_146 : (((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) := by
          apply Or.inr
          intro assump_44
          have assump_147 : True := by
            apply True.intro
          let assump_47 := assump_44 assump_147
          apply False.elim assump_47
        let assump_43 := assump_9 assump_146
        apply False.elim assump_43
  case inr assump_13 =>
    cases assump_10
    case intro assump_56 assump_57 =>
      cases assump_56
      case inl assump_58 =>
        have assump_148 : (((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) := by
          apply Or.inr
          intro assump_67
          have assump_149 : True := by
            apply True.intro
          let assump_70 := assump_67 assump_149
          apply False.elim assump_70
        let assump_66 := assump_9 assump_148
        apply False.elim assump_66
      case inr assump_59 =>
        have assump_150 : (((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) := by
          apply Or.inr
          intro assump_84
          have assump_151 : True := by
            apply True.intro
          let assump_87 := assump_84 assump_151
          apply False.elim assump_87
        let assump_83 := assump_9 assump_150
        apply False.elim assump_83
  intro assump_94
  cases assump_94
  case inl assump_95 =>
    cases assump_95
    case inl assump_97 =>
      have assump_152 : (((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) := by
        apply Or.inr
        intro assump_104
        have assump_153 : True := by
          apply True.intro
        let assump_107 := assump_104 assump_153
        apply False.elim assump_107
      let assump_103 := assump_9 assump_152
      apply False.elim assump_103
    case inr assump_98 =>
      have assump_154 : (((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) := by
        apply Or.inr
        intro assump_119
        have assump_155 : True := by
          apply True.intro
        let assump_122 := assump_119 assump_155
        apply False.elim assump_122
      let assump_118 := assump_9 assump_154
      apply False.elim assump_118
  case inr assump_96 =>
    have assump_156 : (((p5 ∨ p6) ∧ (False ∨ p0)) ∨ ((True → False) → False)) := by
      apply Or.inr
      intro assump_134
      have assump_157 : True := by
        apply True.intro
      let assump_137 := assump_134 assump_157
      apply False.elim assump_137
    let assump_133 := assump_9 assump_156
    apply False.elim assump_133


variable (p1 p7 p4 p5 p6 p3 p2 p0 : Prop)
theorem file10_88983 : (((((True ∨ p1) → False) ∨ ((p6 → False) → (p0 → False))) ∨ (((False ∨ False) → (False ∨ p6)) ∧ ((p5 ∧ p7) ∧ (p4 → p5)))) → ((((False ∨ p4) ∧ (p3 → False)) → ((p1 ∨ p1) → (p2 → p2))) → (((p4 → p4) ∨ (p4 → p4)) ∨ ((False → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_11
      exact assump_11
    case inr assump_8 =>
      apply Or.inl
      apply Or.inl
      intro assump_16
      exact assump_16
  case inr assump_6 =>
    cases assump_6
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply Or.inl
          apply Or.inl
          intro assump_33
          exact assump_33


variable (p1 p7 : Prop)
theorem file10_89891 : (((((False ∧ p1) ∧ (p7 → False)) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∧ p1) ∧ (p7 → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p4 p3 : Prop)
theorem file10_90322 : (((((p4 ∨ p3) ∨ (True ∨ p5)) → ((p3 → p3) ∨ (p3 ∨ p5))) → False) → False) := by
  intro assump_1
  have assump_35 : (((p4 ∨ p3) ∨ (True ∨ p5)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        exact assump_12
      case inr assump_9 =>
        apply Or.inl
        intro assump_17
        exact assump_17
    case inr assump_7 =>
      cases assump_7
      case inl assump_20 =>
        apply Or.inl
        intro assump_24
        exact assump_24
      case inr assump_21 =>
        apply Or.inl
        intro assump_29
        exact assump_29
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p1 : Prop)
theorem file10_91124 : ((((((True ∧ p1) ∨ (p1 → False)) → False) → False) → False) → False) := by
  intro assump_5
  have assump_27 : ((((True ∧ p1) ∨ (p1 → False)) → False) → False) := by
    intro assump_9
    have assump_28 : ((True ∧ p1) ∨ (p1 → False)) := by
      apply Or.inr
      intro assump_13
      have assump_29 : ((True ∧ p1) ∨ (p1 → False)) := by
        apply Or.inl
        apply And.intro
        apply True.intro
        exact assump_13
      let assump_17 := assump_9 assump_29
      apply False.elim assump_17
    let assump_12 := assump_9 assump_28
    apply False.elim assump_12
  let assump_8 := assump_5 assump_27
  apply False.elim assump_8


variable (p5 p3 p4 p0 p2 p6 : Prop)
theorem file10_91829 : (((((p5 ∧ p2) → False) → ((p3 ∧ p6) ∨ (p0 → False))) → False) → ((((p6 → p4) → False) → ((p6 ∧ True) → (p4 → False))) ∨ (((p6 ∧ p3) ∧ (True → p0)) → False))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    have assump_28 : (p6 → p4) := by
      intro assump_22
      exact assump_10
    let assump_21 := assump_8 assump_28
    apply False.elim assump_21


variable (p5 p7 p6 p2 p0 p4 p1 : Prop)
theorem file10_92345 : (((((p7 ∧ p6) → (p2 → False)) → ((True → p4) → (p5 ∨ True))) → False) → ((((p1 ∧ p7) ∧ (p2 → p4)) → False) → (((True ∧ p6) → False) ∧ ((p0 ∧ False) ∨ (p6 ∨ False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_38 : (((p7 ∧ p6) → (p2 → False)) → ((True → p4) → (p5 ∨ True))) := by
      intro assump_15
      intro assump_16
      apply Or.inr
      apply True.intro
    let assump_14 := assump_1 assump_38
    apply False.elim assump_14
  have assump_39 : (((p7 ∧ p6) → (p2 → False)) → ((True → p4) → (p5 ∨ True))) := by
    intro assump_29
    intro assump_30
    apply Or.inr
    apply True.intro
  let assump_28 := assump_1 assump_39
  apply False.elim assump_28


variable (p0 p5 p3 p6 p4 : Prop)
theorem file10_93167 : ((((((False ∨ True) → (p3 ∧ False)) → ((p0 ∨ p6) → False)) ∨ (((p5 ∨ False) ∧ (p4 ∧ p3)) → ((p3 ∧ p0) ∧ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((False ∨ True) → (p3 ∧ False)) → ((p0 ∨ p6) → False)) ∨ (((p5 ∨ False) ∧ (p4 ∧ p3)) → ((p3 ∧ p0) ∧ (p3 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_33 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_13 := assump_5 assump_33
      let assump_14 := And.right assump_13
      apply False.elim assump_14
    case inr assump_8 =>
      have assump_34 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_23 := assump_5 assump_34
      let assump_24 := And.right assump_23
      apply False.elim assump_24
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p7 p3 p5 p6 p0 p4 : Prop)
theorem file10_94136 : ((((((p0 ∧ False) ∧ (p5 → False)) ∧ ((p4 ∨ True) ∨ (False → p6))) → (((p3 → False) ∧ (p5 → False)) → ((p7 ∧ p4) ∨ (p4 → p0)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p0 ∧ False) ∧ (p5 → False)) ∧ ((p4 ∨ True) ∨ (False → p6))) → (((p3 → False) ∧ (p5 → False)) → ((p7 ∧ p4) ∨ (p4 → p0)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p6 p1 p0 p2 p3 p4 p7 p5 : Prop)
theorem file10_94914 : ((((((p0 ∧ p3) ∧ (p2 ∧ p2)) → ((p6 ∧ p0) → False)) → (((True ∧ p0) ∧ (True ∧ True)) ∧ ((p7 ∧ p7) ∨ (True → p7)))) ∧ ((((p7 ∧ p5) → (False ∨ False)) ∧ ((p5 ∧ p2) ∨ (p4 → p2))) ∧ (((True ∨ False) → False) ∧ ((p5 ∨ p5) → (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_7
            case intro assump_20 assump_21 =>
              have assump_45 : (True ∨ False) := by
                apply Or.inl
                apply True.intro
              let assump_28 := assump_20 assump_45
              apply False.elim assump_28
        case inr assump_13 =>
          cases assump_7
          case intro assump_34 assump_35 =>
            have assump_46 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_41 := assump_34 assump_46
            apply False.elim assump_41


variable (p2 p0 p4 p3 p5 p1 p7 : Prop)
theorem file10_96106 : (((((p2 → False) → (p1 → p1)) → False) → (((p3 → False) → (p4 → p5)) → ((p2 → p0) → (p3 → p0)))) ∨ ((((p7 ∨ True) ∨ (True ∧ p3)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  have assump_23 : ((p2 → False) → (p1 → p1)) := by
    intro assump_14
    intro assump_15
    exact assump_15
  let assump_13 := assump_1 assump_23
  apply False.elim assump_13


variable (p5 p3 p1 p0 p2 p4 : Prop)
theorem file10_96582 : ((((((p2 ∧ False) → False) ∧ ((p0 ∨ p5) ∨ (p4 → p3))) → False) ∧ ((((True → p0) ∧ (False ∧ p0)) → ((p5 ∧ p5) ∨ (p5 ∧ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((True → p0) ∧ (False ∧ p0)) → ((p5 ∧ p5) ∨ (p5 ∧ p1))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p2 p7 p5 p4 p3 : Prop)
theorem file10_97193 : (((((True ∨ p3) → (p2 → p5)) ∧ ((p2 ∧ p2) → (p7 → False))) → (((False → p7) → False) → False)) ∨ ((((p2 → p4) ∨ (False → False)) ∨ ((p5 ∨ True) ∨ (False → False))) ∨ (((False → False) → False) → False))) := by
  apply Or.inl
  intro assump_35
  intro assump_36
  cases assump_35
  case intro assump_39 assump_40 =>
    have assump_55 : (False → p7) := by
      intro assump_49
      apply False.elim assump_49
    let assump_48 := assump_36 assump_55
    apply False.elim assump_48


variable (p7 p4 p6 p2 p0 p1 p3 : Prop)
theorem file10_97738 : ((((((p7 ∨ p1) ∨ (p2 → False)) → ((False ∧ p1) → (p2 → False))) ∧ (((p0 → p7) ∨ (p6 ∨ p4)) → False)) ∧ ((((p1 ∨ p3) → False) → False) ∧ (((p2 ∨ p0) ∧ (p6 → False)) ∧ ((False → p7) → False)))) → False) := by
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
            cases assump_16
            case inl assump_18 =>
              have assump_46 : (False → p7) := by
                intro assump_27
                apply False.elim assump_27
              let assump_26 := assump_15 assump_46
              apply False.elim assump_26
            case inr assump_19 =>
              have assump_47 : (False → p7) := by
                intro assump_40
                apply False.elim assump_40
              let assump_39 := assump_15 assump_47
              apply False.elim assump_39


variable (p6 p4 p0 p2 p5 p1 : Prop)
theorem file10_98855 : ((((((p4 ∧ p1) ∧ (False ∧ p2)) → ((p6 ∨ p2) → (p5 → p6))) → (((True → False) ∨ (False ∧ p1)) → ((p0 → True) ∨ (p2 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p4 ∧ p1) ∧ (False ∧ p2)) → ((p6 ∨ p2) → (p5 → p6))) → (((True → False) ∨ (False ∧ p1)) → ((p0 → True) ∨ (p2 ∨ p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p1 p3 p2 p6 p0 : Prop)
theorem file10_99557 : (((((True → p0) ∨ (p0 ∧ p4)) → False) → (((p6 → False) → (p3 ∨ True)) → ((p6 ∧ p0) → False))) ∨ ((((p2 ∧ p3) → False) → ((p2 ∧ p4) → (p1 → False))) ∨ (((p6 → False) → False) ∧ ((False → False) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_21 : ((True → p0) ∨ (p0 ∧ p4)) := by
      apply Or.inl
      intro assump_15
      exact assump_5
    let assump_14 := assump_1 assump_21
    apply False.elim assump_14


variable (p4 p6 p7 p3 p2 p1 p0 : Prop)
theorem file10_100141 : (((((p0 → False) → (p2 → True)) → False) ∨ (((p4 → p0) → False) ∧ ((p0 ∧ p0) → False))) → ((((True → False) ∧ (p6 ∧ p2)) ∧ ((p7 → False) → (True ∨ p4))) → (((False ∧ p2) ∨ (p1 ∧ p4)) ∨ ((True → False) → (p3 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_1
        case inl assump_17 =>
          apply Or.inr
          intro assump_21
          apply And.intro
          have assump_53 : True := by
            apply True.intro
          let assump_24 := assump_21 assump_53
          apply False.elim assump_24
          have assump_54 : True := by
            apply True.intro
          let assump_30 := assump_21 assump_54
          apply False.elim assump_30
        case inr assump_18 =>
          cases assump_18
          case intro assump_34 assump_35 =>
            apply Or.inr
            intro assump_40
            apply And.intro
            have assump_55 : True := by
              apply True.intro
            let assump_43 := assump_40 assump_55
            apply False.elim assump_43
            have assump_56 : True := by
              apply True.intro
            let assump_49 := assump_40 assump_56
            apply False.elim assump_49


variable (p1 p7 p6 p2 p3 p4 : Prop)
theorem file10_101553 : (((((False ∧ p6) → False) → False) → (((p6 → False) → False) ∨ ((p7 ∧ p1) ∨ (p6 ∧ p1)))) ∨ ((((p3 → p4) ∧ (False ∧ p2)) → ((p1 ∨ p4) → False)) ∨ (((p2 ∧ p3) ∨ (False → False)) → ((p6 ∨ True) → (p6 ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_17 : ((False ∧ p6) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_8 := assump_1 assump_17
  apply False.elim assump_8


variable (p3 p6 p2 p1 p4 : Prop)
theorem file10_102109 : (((((True ∧ p4) ∨ (True ∨ True)) ∨ ((p2 → False) ∨ (p2 ∧ p3))) → False) → ((((p1 ∨ p2) → (p6 → True)) ∧ ((True → False) → False)) → (((False ∧ p3) → (p3 ∧ p3)) ∧ ((p4 → False) ∧ (False → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  cases assump_3
  case intro assump_8 assump_9 =>
    apply False.elim assump_8
  apply And.intro
  intro assump_12
  cases assump_2
  case intro assump_15 assump_16 =>
    have assump_30 : (((True ∧ p4) ∨ (True ∨ True)) ∨ ((p2 → False) ∨ (p2 ∧ p3))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      apply True.intro
      exact assump_12
    let assump_23 := assump_1 assump_30
    apply False.elim assump_23
  intro assump_27
  apply False.elim assump_27


variable (p0 p5 p7 p3 p2 p6 p4 p1 : Prop)
theorem file10_103028 : (((((True ∧ p1) → (False → p7)) → False) → (((p4 → False) → (p2 → p5)) ∨ ((p3 → False) → (False → False)))) ∨ ((((False → False) ∧ (False → p0)) → ((p7 ∧ p1) ∧ (False ∨ p2))) ∧ (((p6 → True) ∧ (p1 ∨ p2)) ∧ ((p4 ∨ True) → (p3 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_20 : ((True ∧ p1) → (False → p7)) := by
    intro assump_13
    intro assump_14
    apply False.elim assump_14
  let assump_12 := assump_1 assump_20
  apply False.elim assump_12


variable (p1 p4 p0 p3 p2 p5 p7 : Prop)
theorem file10_103605 : (((((True ∧ False) ∧ (p7 → False)) → False) ∨ (((True → False) ∨ (p2 → False)) ∧ ((p3 → False) ∨ (False → p5)))) ∨ ((((p2 → p3) ∨ (p0 ∨ p5)) → ((p7 ∧ True) → False)) ∨ (((p4 → p3) → (p4 → p4)) ∨ ((p0 ∨ p1) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      apply False.elim assump_19


variable (p6 p2 p4 p1 p5 : Prop)
theorem file10_104079 : (((((p6 → False) → (p4 ∨ p1)) → ((p1 ∧ p2) → False)) → (((True ∧ p5) → (True ∨ True)) → ((p6 → False) → (p6 → False)))) ∨ ((((p4 → False) ∧ (p6 ∧ True)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  have assump_27 : p6 := by
    exact assump_4
  let assump_23 := assump_3 assump_27
  apply False.elim assump_23


variable (p6 p2 p0 p7 p3 p4 p5 : Prop)
theorem file10_104517 : (((((False → p3) ∧ (p2 ∧ p3)) ∧ ((p6 ∧ p5) → (p7 ∧ True))) → (((p7 → p6) ∧ (False ∨ p4)) → ((p0 → p0) ∨ (p4 → False)))) ∨ ((((p4 ∧ p7) → (p7 → False)) ∧ ((p0 → False) ∧ (False ∨ p0))) → (((p7 ∧ p0) ∧ (p3 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      apply False.elim assump_7
    case inr assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            apply Or.inl
            intro assump_27
            exact assump_27


variable (p2 p5 p0 p7 p4 p3 : Prop)
theorem file10_105287 : (((((p4 → p0) → False) ∨ ((p7 ∧ p2) ∨ (p4 ∧ p0))) → (((p3 → p3) ∨ (True → p0)) ∨ ((p5 → False) → (p7 ∨ False)))) ∨ ((((p2 → False) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    exact assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inl
        intro assump_17
        exact assump_17
    case inr assump_10 =>
      cases assump_10
      case intro assump_20 assump_21 =>
        apply Or.inl
        apply Or.inl
        intro assump_26
        exact assump_26


variable (p3 p4 p6 p0 p2 p5 p7 p1 : Prop)
theorem file10_106058 : (((((p0 ∧ p0) ∧ (False ∧ p7)) → ((p6 ∨ p1) ∨ (True → False))) ∨ (((p2 ∨ p2) → (p3 → True)) → ((p6 ∧ p4) ∧ (p3 ∨ p7)))) ∨ ((((p5 → False) ∧ (p0 → p2)) ∨ ((p6 ∨ False) ∧ (p5 ∨ p0))) → (((False ∧ p6) → (p7 ∨ p0)) → ((p1 ∨ False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply False.elim assump_10


variable (p4 p2 p1 p0 p7 p3 p5 : Prop)
theorem file10_106614 : (((((p2 ∨ p0) ∨ (p2 → p4)) → ((p4 ∧ p4) → (True ∨ p7))) → False) → ((((True → p5) ∨ (True ∨ p5)) → ((p7 → p1) ∧ (p7 ∧ p3))) → (((p2 ∨ p2) ∨ (True ∧ p3)) → ((p0 ∧ p7) ∨ (False → p7))))) := by
  intro assump_30
  intro assump_31
  intro assump_32
  cases assump_32
  case inl assump_33 =>
    cases assump_33
    case inl assump_35 =>
      apply Or.inr
      intro assump_43
      apply False.elim assump_43
    case inr assump_36 =>
      apply Or.inr
      intro assump_52
      apply False.elim assump_52
  case inr assump_34 =>
    cases assump_34
    case intro assump_55 assump_56 =>
      apply Or.inr
      intro assump_65
      apply False.elim assump_65


variable (p4 p1 p5 p3 p6 p2 : Prop)
theorem file10_107337 : ((((((p1 ∧ p5) ∧ (p5 → False)) ∧ ((p6 ∧ p3) → (p4 ∨ p2))) → False) ∧ ((((False → False) ∧ (p3 → p3)) → False) ∧ (((p3 ∨ p6) ∨ (p3 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_24 : ((p3 ∨ p6) ∨ (p3 → False)) := by
        apply Or.inr
        intro assump_13
        have assump_25 : ((p3 ∨ p6) ∨ (p3 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_13
        let assump_17 := assump_7 assump_25
        apply False.elim assump_17
      let assump_12 := assump_7 assump_24
      apply False.elim assump_12


variable (p2 p1 p5 p4 p3 p0 p7 p6 : Prop)
theorem file10_108077 : (((((p7 ∧ p2) ∨ (False → p2)) → ((p2 ∨ p3) ∧ (p5 ∨ p7))) ∨ (((p2 → p0) → (p0 ∧ p3)) ∨ ((p7 ∨ p1) ∧ (p3 → p4)))) → ((((p6 ∧ False) → (p6 ∧ p5)) ∨ ((False ∧ p4) ∧ (p0 → False))) ∨ (((True ∨ False) → (p6 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  case inr assump_3 =>
    cases assump_3
    case inl assump_19 =>
      apply Or.inl
      apply Or.inl
      intro assump_23
      apply And.intro
      cases assump_23
      case intro assump_24 assump_25 =>
        apply False.elim assump_25
      cases assump_23
      case intro assump_30 assump_31 =>
        apply False.elim assump_31
    case inr assump_20 =>
      cases assump_20
      case intro assump_36 assump_37 =>
        cases assump_36
        case inl assump_38 =>
          apply Or.inl
          apply Or.inl
          intro assump_44
          apply And.intro
          cases assump_44
          case intro assump_45 assump_46 =>
            apply False.elim assump_46
          cases assump_44
          case intro assump_51 assump_52 =>
            apply False.elim assump_52
        case inr assump_39 =>
          apply Or.inl
          apply Or.inl
          intro assump_61
          apply And.intro
          cases assump_61
          case intro assump_62 assump_63 =>
            apply False.elim assump_63
          cases assump_61
          case intro assump_68 assump_69 =>
            apply False.elim assump_69


variable (p2 p0 : Prop)
theorem file10_109808 : ((((((p0 → p2) → False) ∧ ((p2 ∨ True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p0 → p2) → False) ∧ ((p2 ∨ True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : (p2 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p5 p0 p6 p7 p4 p3 p1 : Prop)
theorem file10_110355 : (((((p0 ∧ p6) → (p3 ∨ p6)) ∨ ((p4 → p0) ∧ (p0 → False))) ∨ (((p0 ∨ p7) → False) → False)) ∨ ((((p4 → p1) ∧ (False ∧ False)) ∧ ((p4 ∧ p3) → (p2 ∧ p0))) ∧ (((p0 → p1) → (p7 ∨ p5)) ∨ ((p5 ∧ p3) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    exact assump_3


variable (p4 p0 p6 p3 p7 p1 p5 p2 : Prop)
theorem file10_110779 : ((((((p4 → False) ∧ (False ∧ True)) → ((p0 ∧ p0) ∧ (p7 ∨ p3))) ∨ (((p2 → False) ∧ (p6 → p1)) ∧ ((p6 → False) → (p4 → p5)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p4 → False) ∧ (False ∧ True)) → ((p0 ∧ p0) ∧ (p7 ∨ p3))) ∨ (((p2 → False) ∧ (p6 → p1)) ∧ ((p6 → False) → (p4 → p5)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    cases assump_5
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
    cases assump_5
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p3 p5 p1 p0 p4 : Prop)
theorem file10_111748 : (((((True ∧ True) ∧ (True → False)) → False) → False) → ((((p0 ∧ p0) → (p0 ∨ p4)) ∨ ((p1 ∨ p3) → False)) ∨ (((p1 → p5) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    exact assump_6


variable (p4 p1 p6 p7 p2 p3 p5 : Prop)
theorem file10_112107 : ((((((p5 → False) → (p4 → p6)) → ((p6 → p6) ∨ (p2 ∨ False))) → False) ∧ ((((p1 ∧ True) → False) ∧ ((p6 → p6) → False)) ∧ (((False → False) ∧ (p3 ∧ p1)) ∨ ((p5 → False) ∨ (False ∨ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_62 : (p6 → p6) := by
                intro assump_30
                exact assump_30
              let assump_29 := assump_9 assump_62
              apply False.elim assump_29
        case inr assump_15 =>
          cases assump_15
          case inl assump_36 =>
            have assump_63 : (p6 → p6) := by
              intro assump_42
              exact assump_42
            let assump_41 := assump_9 assump_63
            apply False.elim assump_41
          case inr assump_37 =>
            cases assump_37
            case inl assump_48 =>
              apply False.elim assump_48
            case inr assump_49 =>
              have assump_64 : (p6 → p6) := by
                intro assump_56
                exact assump_56
              let assump_55 := assump_9 assump_64
              apply False.elim assump_55


variable (p0 p7 p1 p5 p2 p4 p6 p3 : Prop)
theorem file10_113607 : (((((False → p7) ∧ (p4 → p2)) ∧ ((False → False) → False)) → False) ∧ ((((p5 ∨ p6) ∧ (p3 ∨ p2)) → False) → (((p0 ∧ p0) → (True → True)) ∨ ((p0 ∨ p1) ∧ (p5 ∨ p4))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_24 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_3 assump_24
      apply False.elim assump_12
  intro assump_19
  apply Or.inl
  intro assump_22
  intro assump_23
  apply True.intro


variable (p4 p1 p3 p5 p7 : Prop)
theorem file10_114243 : ((((((p3 → False) → False) → ((p5 → False) → False)) → False) ∧ ((((p7 ∨ p1) ∧ (True → False)) → ((p1 ∨ p1) ∨ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_33 : (((p7 ∨ p1) ∧ (True → False)) → ((p1 ∨ p1) ∨ (p4 → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inr
          intro assump_18
          have assump_34 : True := by
            apply True.intro
          let assump_22 := assump_11 assump_34
          apply False.elim assump_22
        case inr assump_13 =>
          apply Or.inl
          apply Or.inl
          exact assump_13
    let assump_8 := assump_3 assump_33
    apply False.elim assump_8


variable (p4 p7 p5 p1 p0 p2 : Prop)
theorem file10_115115 : (((((p1 ∧ p5) → (False → False)) → False) → (((p2 → False) → False) → False)) ∨ ((((p5 → p0) → (p7 → p4)) ∧ ((False ∧ p5) → (True → False))) ∧ (((p1 ∧ True) → (p1 → p1)) ∧ ((p7 → False) → (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_15 : ((p1 ∧ p5) → (False → False)) := by
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_15
  apply False.elim assump_7


variable (p5 p7 p1 p0 p4 p2 p6 p3 : Prop)
theorem file10_115629 : (((((p1 ∧ p5) ∧ (p7 ∧ p0)) ∧ ((True ∨ p1) → (True → False))) → (((True → p7) → (p3 ∧ p2)) → False)) ∨ ((((p7 ∨ False) ∨ (p3 ∨ p4)) → False) ∧ (((p4 ∧ p4) ∨ (p6 ∨ p5)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          have assump_28 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_23 := assump_6 assump_28
          have assump_29 : True := by
            apply True.intro
          let assump_24 := assump_23 assump_29
          apply False.elim assump_24


variable (p1 p2 p7 p0 p6 p5 p3 : Prop)
theorem file10_116452 : ((((((p3 → p6) → (p1 → False)) → ((p5 ∨ p1) ∨ (p1 → False))) → (((p5 ∧ p5) → (p7 → p1)) → ((p3 ∨ p0) → (True → False)))) ∧ ((((p3 ∨ p0) ∧ (False → True)) ∨ ((True → False) → False)) ∧ (((True ∧ p2) ∧ (p6 ∧ p1)) ∧ ((p1 ∧ p3) ∧ (p6 → False))))) → False) := by
  intro assump_49
  cases assump_49
  case intro assump_50 assump_51 =>
    cases assump_51
    case intro assump_54 assump_55 =>
      cases assump_54
      case inl assump_56 =>
        cases assump_56
        case intro assump_58 assump_59 =>
          cases assump_58
          case inl assump_60 =>
            cases assump_55
            case intro assump_66 assump_67 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                cases assump_68
                case intro assump_70 assump_71 =>
                  cases assump_69
                  case intro assump_76 assump_77 =>
                    cases assump_67
                    case intro assump_82 assump_83 =>
                      cases assump_82
                      case intro assump_84 assump_85 =>
                        have assump_162 : p6 := by
                          exact assump_76
                        let assump_92 := assump_83 assump_162
                        apply False.elim assump_92
          case inr assump_61 =>
            cases assump_55
            case intro assump_100 assump_101 =>
              cases assump_100
              case intro assump_102 assump_103 =>
                cases assump_102
                case intro assump_104 assump_105 =>
                  cases assump_103
                  case intro assump_110 assump_111 =>
                    cases assump_101
                    case intro assump_116 assump_117 =>
                      cases assump_116
                      case intro assump_118 assump_119 =>
                        have assump_163 : p6 := by
                          exact assump_110
                        let assump_126 := assump_117 assump_163
                        apply False.elim assump_126
      case inr assump_57 =>
        cases assump_55
        case intro assump_132 assump_133 =>
          cases assump_132
          case intro assump_134 assump_135 =>
            cases assump_134
            case intro assump_136 assump_137 =>
              cases assump_135
              case intro assump_142 assump_143 =>
                cases assump_133
                case intro assump_148 assump_149 =>
                  cases assump_148
                  case intro assump_150 assump_151 =>
                    have assump_164 : p6 := by
                      exact assump_142
                    let assump_158 := assump_149 assump_164
                    apply False.elim assump_158


variable (p1 p2 p4 p5 : Prop)
theorem file10_119236 : (((((p1 ∨ p4) → False) ∧ ((False ∨ p4) ∧ (p4 ∧ True))) → False) ∨ ((((True ∧ True) → (p5 → p2)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          have assump_26 : (p1 ∨ p4) := by
            apply Or.inr
            exact assump_14
          let assump_22 := assump_2 assump_26
          apply False.elim assump_22


variable (p6 p7 p1 p0 : Prop)
theorem file10_119902 : ((((((True ∨ p0) → False) → False) ∨ (((p6 → p1) ∧ (p7 ∧ p7)) → False)) → False) → False) := by
  intro assump_5
  have assump_19 : ((((True ∨ p0) → False) → False) ∨ (((p6 → p1) ∧ (p7 ∧ p7)) → False)) := by
    apply Or.inl
    intro assump_9
    have assump_20 : (True ∨ p0) := by
      apply Or.inl
      apply True.intro
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p0 p2 p6 p4 p3 p1 p7 : Prop)
theorem file10_120426 : (((((p2 ∧ False) ∧ (p0 ∨ p6)) ∧ ((p3 ∨ p3) ∨ (p0 → p4))) → False) ∨ ((((p4 → False) ∨ (p7 → False)) → ((False → True) ∧ (p1 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7


variable (p5 p3 p6 p0 p7 : Prop)
theorem file10_120862 : (((((p0 ∨ p6) ∨ (p0 → False)) → False) → False) ∨ ((((p6 → False) → False) → False) ∧ (((p3 ∧ p0) → (p7 ∨ p5)) ∨ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_16 : ((p0 ∨ p6) ∨ (p0 → False)) := by
    apply Or.inr
    intro assump_5
    have assump_17 : ((p0 ∨ p6) ∨ (p0 → False)) := by
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p4 p0 : Prop)
theorem file10_121425 : (((((p0 ∨ p0) ∨ (p4 → False)) ∧ ((p6 ∧ False) ∧ (False ∨ True))) ∧ (((p0 → False) → (False ∧ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
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
              apply False.elim assump_15
        case inr assump_9 =>
          cases assump_5
          case intro assump_22 assump_23 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
      case inr assump_7 =>
        cases assump_5
        case intro assump_32 assump_33 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            apply False.elim assump_35


variable (p5 p0 p3 p6 p7 p1 p2 : Prop)
theorem file10_122432 : (((((p5 ∨ True) ∧ (p3 → False)) ∨ ((p3 → p3) → (True ∧ p0))) ∨ (((p1 ∨ p6) ∧ (p7 ∨ False)) ∧ ((False → p6) ∧ (p7 ∧ p6)))) → ((((False → True) → False) → False) ∨ (((p3 → False) ∨ (p3 ∨ p7)) ∨ ((p3 → False) ∧ (p6 ∨ p2))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          intro assump_14
          have assump_102 : (False → True) := by
            intro assump_18
            apply True.intro
          let assump_17 := assump_14 assump_102
          apply False.elim assump_17
        case inr assump_9 =>
          apply Or.inl
          intro assump_26
          have assump_103 : (False → True) := by
            intro assump_30
            apply True.intro
          let assump_29 := assump_26 assump_103
          apply False.elim assump_29
    case inr assump_5 =>
      apply Or.inl
      intro assump_36
      have assump_104 : (False → True) := by
        intro assump_40
        apply True.intro
      let assump_39 := assump_36 assump_104
      apply False.elim assump_39
  case inr assump_3 =>
    cases assump_3
    case intro assump_44 assump_45 =>
      cases assump_44
      case intro assump_46 assump_47 =>
        cases assump_46
        case inl assump_48 =>
          cases assump_47
          case inl assump_52 =>
            cases assump_45
            case intro assump_56 assump_57 =>
              cases assump_57
              case intro assump_60 assump_61 =>
                apply Or.inl
                intro assump_66
                have assump_105 : (False → True) := by
                  intro assump_70
                  apply True.intro
                let assump_69 := assump_66 assump_105
                apply False.elim assump_69
          case inr assump_53 =>
            apply False.elim assump_53
        case inr assump_49 =>
          cases assump_47
          case inl assump_78 =>
            cases assump_45
            case intro assump_82 assump_83 =>
              cases assump_83
              case intro assump_86 assump_87 =>
                apply Or.inl
                intro assump_92
                have assump_106 : (False → True) := by
                  intro assump_96
                  apply True.intro
                let assump_95 := assump_92 assump_106
                apply False.elim assump_95
          case inr assump_79 =>
            apply False.elim assump_79


