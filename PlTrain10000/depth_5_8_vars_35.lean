variable (p1 p0 p6 p5 p7 p4 : Prop)
theorem file35_44 : ((((((True → False) ∧ (p5 ∧ True)) → ((p0 ∨ p1) ∧ (p6 ∨ True))) ∨ (((p5 ∨ p6) → (False → False)) ∨ ((p1 ∨ p7) → (p5 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((True → False) ∧ (p5 ∧ True)) → ((p0 ∨ p1) ∧ (p6 ∨ True))) ∨ (((p5 ∨ p6) → (False → False)) ∨ ((p1 ∨ p7) → (p5 ∨ p4)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_35 : True := by
          apply True.intro
        let assump_17 := assump_6 assump_35
        apply False.elim assump_17
    cases assump_5
    case intro assump_21 assump_22 =>
      cases assump_22
      case intro assump_25 assump_26 =>
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p5 p4 p6 p2 p1 p7 p0 : Prop)
theorem file35_965 : (((((p2 ∨ p7) → (p2 → False)) ∨ ((p6 → False) → False)) → False) → ((((False → p1) ∨ (False → p6)) ∧ ((p2 → p2) ∨ (p5 → p2))) ∨ (((p6 ∧ p5) → (p0 → p2)) ∨ ((p1 ∨ p4) → (p1 → False))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  intro assump_7
  exact assump_7


variable (p2 p7 p4 p1 p6 p3 : Prop)
theorem file35_1375 : (((((p7 → p2) ∨ (p4 ∧ p7)) → ((p6 ∧ p7) ∨ (p4 ∧ p7))) ∨ (((True ∨ True) → (p2 → p4)) → ((p4 → False) ∨ (p2 ∧ False)))) → ((((p4 ∧ p3) → False) → ((p3 ∨ False) ∨ (p4 → p4))) ∨ (((p6 → False) → (p1 ∧ True)) ∨ ((False → False) → (p6 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply Or.inr
    intro assump_9
    exact assump_9
  case inr assump_3 =>
    apply Or.inl
    intro assump_14
    apply Or.inr
    intro assump_17
    exact assump_17


variable (p5 p0 : Prop)
theorem file35_1937 : ((((((False → True) → False) → False) ∨ (((p0 → False) ∧ (p5 → False)) ∧ ((False ∧ True) → False))) → False) → False) := by
  intro assump_23
  have assump_38 : ((((False → True) → False) → False) ∨ (((p0 → False) ∧ (p5 → False)) ∧ ((False ∧ True) → False))) := by
    apply Or.inl
    intro assump_27
    have assump_39 : (False → True) := by
      intro assump_31
      apply True.intro
    let assump_30 := assump_27 assump_39
    apply False.elim assump_30
  let assump_26 := assump_23 assump_38
  apply False.elim assump_26


variable (p1 p3 p6 p2 p7 p4 : Prop)
theorem file35_2526 : (((((p4 ∨ p2) → (p3 → p3)) → False) → (((p6 → False) ∧ (p6 ∨ p7)) → False)) ∨ ((((p4 → p3) ∨ (p1 → p2)) → ((True → False) ∧ (p1 → p1))) → False)) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case inl assump_11 =>
      have assump_49 : ((p4 ∨ p2) → (p3 → p3)) := by
        intro assump_18
        intro assump_19
        cases assump_18
        case inl assump_22 =>
          exact assump_19
        case inr assump_23 =>
          exact assump_19
      let assump_17 := assump_5 assump_49
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_50 : ((p4 ∨ p2) → (p3 → p3)) := by
        intro assump_36
        intro assump_37
        cases assump_36
        case inl assump_40 =>
          exact assump_37
        case inr assump_41 =>
          exact assump_37
      let assump_35 := assump_5 assump_50
      apply False.elim assump_35


variable (p4 p6 p7 p2 p1 p5 : Prop)
theorem file35_3533 : ((((((p1 → False) ∧ (p1 ∧ p7)) ∧ ((False → p5) ∧ (p4 ∨ p2))) ∧ (((p2 ∨ p6) ∨ (p5 → p4)) ∨ ((p5 → True) → False))) ∧ ((((True ∧ p1) → False) ∨ ((p6 → False) ∧ (p4 → False))) ∧ (((p4 → False) ∨ (p7 → False)) ∨ ((True → True) ∧ (p6 ∧ p2))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              cases assump_23
              case inl assump_26 =>
                cases assump_9
                case inl assump_30 =>
                  cases assump_30
                  case inl assump_32 =>
                    cases assump_32
                    case inl assump_34 =>
                      cases assump_7
                      case intro assump_38 assump_39 =>
                        cases assump_38
                        case inl assump_40 =>
                          cases assump_39
                          case inl assump_44 =>
                            cases assump_44
                            case inl assump_46 =>
                              have assump_730 : p4 := by
                                exact assump_26
                              let assump_50 := assump_46 assump_730
                              apply False.elim assump_50
                            case inr assump_47 =>
                              have assump_731 : p7 := by
                                exact assump_17
                              let assump_56 := assump_47 assump_731
                              apply False.elim assump_56
                          case inr assump_45 =>
                            cases assump_45
                            case intro assump_60 assump_61 =>
                              cases assump_61
                              case intro assump_64 assump_65 =>
                                have assump_732 : (True ∧ p1) := by
                                  apply And.intro
                                  apply True.intro
                                  exact assump_16
                                let assump_74 := assump_40 assump_732
                                apply False.elim assump_74
                        case inr assump_41 =>
                          cases assump_41
                          case intro assump_78 assump_79 =>
                            cases assump_39
                            case inl assump_84 =>
                              cases assump_84
                              case inl assump_86 =>
                                have assump_733 : p4 := by
                                  exact assump_26
                                let assump_90 := assump_86 assump_733
                                apply False.elim assump_90
                              case inr assump_87 =>
                                have assump_734 : p7 := by
                                  exact assump_17
                                let assump_96 := assump_87 assump_734
                                apply False.elim assump_96
                            case inr assump_85 =>
                              cases assump_85
                              case intro assump_100 assump_101 =>
                                cases assump_101
                                case intro assump_104 assump_105 =>
                                  have assump_735 : p4 := by
                                    exact assump_26
                                  let assump_114 := assump_79 assump_735
                                  apply False.elim assump_114
                    case inr assump_35 =>
                      cases assump_7
                      case intro assump_120 assump_121 =>
                        cases assump_120
                        case inl assump_122 =>
                          cases assump_121
                          case inl assump_126 =>
                            cases assump_126
                            case inl assump_128 =>
                              have assump_736 : p4 := by
                                exact assump_26
                              let assump_132 := assump_128 assump_736
                              apply False.elim assump_132
                            case inr assump_129 =>
                              have assump_737 : p7 := by
                                exact assump_17
                              let assump_138 := assump_129 assump_737
                              apply False.elim assump_138
                          case inr assump_127 =>
                            cases assump_127
                            case intro assump_142 assump_143 =>
                              cases assump_143
                              case intro assump_146 assump_147 =>
                                have assump_738 : (True ∧ p1) := by
                                  apply And.intro
                                  apply True.intro
                                  exact assump_16
                                let assump_156 := assump_122 assump_738
                                apply False.elim assump_156
                        case inr assump_123 =>
                          cases assump_123
                          case intro assump_160 assump_161 =>
                            cases assump_121
                            case inl assump_166 =>
                              cases assump_166
                              case inl assump_168 =>
                                have assump_739 : p4 := by
                                  exact assump_26
                                let assump_172 := assump_168 assump_739
                                apply False.elim assump_172
                              case inr assump_169 =>
                                have assump_740 : p7 := by
                                  exact assump_17
                                let assump_178 := assump_169 assump_740
                                apply False.elim assump_178
                            case inr assump_167 =>
                              cases assump_167
                              case intro assump_182 assump_183 =>
                                cases assump_183
                                case intro assump_186 assump_187 =>
                                  have assump_741 : p4 := by
                                    exact assump_26
                                  let assump_196 := assump_161 assump_741
                                  apply False.elim assump_196
                  case inr assump_33 =>
                    cases assump_7
                    case intro assump_202 assump_203 =>
                      cases assump_202
                      case inl assump_204 =>
                        cases assump_203
                        case inl assump_208 =>
                          cases assump_208
                          case inl assump_210 =>
                            have assump_742 : p4 := by
                              exact assump_26
                            let assump_214 := assump_210 assump_742
                            apply False.elim assump_214
                          case inr assump_211 =>
                            have assump_743 : p7 := by
                              exact assump_17
                            let assump_220 := assump_211 assump_743
                            apply False.elim assump_220
                        case inr assump_209 =>
                          cases assump_209
                          case intro assump_224 assump_225 =>
                            cases assump_225
                            case intro assump_228 assump_229 =>
                              have assump_744 : (True ∧ p1) := by
                                apply And.intro
                                apply True.intro
                                exact assump_16
                              let assump_238 := assump_204 assump_744
                              apply False.elim assump_238
                      case inr assump_205 =>
                        cases assump_205
                        case intro assump_242 assump_243 =>
                          cases assump_203
                          case inl assump_248 =>
                            cases assump_248
                            case inl assump_250 =>
                              have assump_745 : p4 := by
                                exact assump_26
                              let assump_254 := assump_250 assump_745
                              apply False.elim assump_254
                            case inr assump_251 =>
                              have assump_746 : p7 := by
                                exact assump_17
                              let assump_260 := assump_251 assump_746
                              apply False.elim assump_260
                          case inr assump_249 =>
                            cases assump_249
                            case intro assump_264 assump_265 =>
                              cases assump_265
                              case intro assump_268 assump_269 =>
                                have assump_747 : p4 := by
                                  exact assump_26
                                let assump_278 := assump_243 assump_747
                                apply False.elim assump_278
                case inr assump_31 =>
                  cases assump_7
                  case intro assump_284 assump_285 =>
                    cases assump_284
                    case inl assump_286 =>
                      cases assump_285
                      case inl assump_290 =>
                        cases assump_290
                        case inl assump_292 =>
                          have assump_748 : p4 := by
                            exact assump_26
                          let assump_296 := assump_292 assump_748
                          apply False.elim assump_296
                        case inr assump_293 =>
                          have assump_749 : p7 := by
                            exact assump_17
                          let assump_302 := assump_293 assump_749
                          apply False.elim assump_302
                      case inr assump_291 =>
                        cases assump_291
                        case intro assump_306 assump_307 =>
                          cases assump_307
                          case intro assump_310 assump_311 =>
                            have assump_750 : (True ∧ p1) := by
                              apply And.intro
                              apply True.intro
                              exact assump_16
                            let assump_320 := assump_286 assump_750
                            apply False.elim assump_320
                    case inr assump_287 =>
                      cases assump_287
                      case intro assump_324 assump_325 =>
                        cases assump_285
                        case inl assump_330 =>
                          cases assump_330
                          case inl assump_332 =>
                            have assump_751 : p4 := by
                              exact assump_26
                            let assump_336 := assump_332 assump_751
                            apply False.elim assump_336
                          case inr assump_333 =>
                            have assump_752 : p7 := by
                              exact assump_17
                            let assump_342 := assump_333 assump_752
                            apply False.elim assump_342
                        case inr assump_331 =>
                          cases assump_331
                          case intro assump_346 assump_347 =>
                            cases assump_347
                            case intro assump_350 assump_351 =>
                              have assump_753 : p4 := by
                                exact assump_26
                              let assump_360 := assump_325 assump_753
                              apply False.elim assump_360
              case inr assump_27 =>
                cases assump_9
                case inl assump_366 =>
                  cases assump_366
                  case inl assump_368 =>
                    cases assump_368
                    case inl assump_370 =>
                      cases assump_7
                      case intro assump_374 assump_375 =>
                        cases assump_374
                        case inl assump_376 =>
                          cases assump_375
                          case inl assump_380 =>
                            cases assump_380
                            case inl assump_382 =>
                              have assump_754 : (True ∧ p1) := by
                                apply And.intro
                                apply True.intro
                                exact assump_16
                              let assump_387 := assump_376 assump_754
                              apply False.elim assump_387
                            case inr assump_383 =>
                              have assump_755 : p7 := by
                                exact assump_17
                              let assump_393 := assump_383 assump_755
                              apply False.elim assump_393
                          case inr assump_381 =>
                            cases assump_381
                            case intro assump_397 assump_398 =>
                              cases assump_398
                              case intro assump_401 assump_402 =>
                                have assump_756 : (True ∧ p1) := by
                                  apply And.intro
                                  apply True.intro
                                  exact assump_16
                                let assump_411 := assump_376 assump_756
                                apply False.elim assump_411
                        case inr assump_377 =>
                          cases assump_377
                          case intro assump_415 assump_416 =>
                            cases assump_375
                            case inl assump_421 =>
                              cases assump_421
                              case inl assump_423 =>
                                have assump_757 : p1 := by
                                  exact assump_16
                                let assump_435 := assump_12 assump_757
                                apply False.elim assump_435
                              case inr assump_424 =>
                                have assump_758 : p7 := by
                                  exact assump_17
                                let assump_441 := assump_424 assump_758
                                apply False.elim assump_441
                            case inr assump_422 =>
                              cases assump_422
                              case intro assump_445 assump_446 =>
                                cases assump_446
                                case intro assump_449 assump_450 =>
                                  have assump_759 : p6 := by
                                    exact assump_449
                                  let assump_460 := assump_415 assump_759
                                  apply False.elim assump_460
                    case inr assump_371 =>
                      cases assump_7
                      case intro assump_466 assump_467 =>
                        cases assump_466
                        case inl assump_468 =>
                          cases assump_467
                          case inl assump_472 =>
                            cases assump_472
                            case inl assump_474 =>
                              have assump_760 : (True ∧ p1) := by
                                apply And.intro
                                apply True.intro
                                exact assump_16
                              let assump_479 := assump_468 assump_760
                              apply False.elim assump_479
                            case inr assump_475 =>
                              have assump_761 : p7 := by
                                exact assump_17
                              let assump_485 := assump_475 assump_761
                              apply False.elim assump_485
                          case inr assump_473 =>
                            cases assump_473
                            case intro assump_489 assump_490 =>
                              cases assump_490
                              case intro assump_493 assump_494 =>
                                have assump_762 : (True ∧ p1) := by
                                  apply And.intro
                                  apply True.intro
                                  exact assump_16
                                let assump_503 := assump_468 assump_762
                                apply False.elim assump_503
                        case inr assump_469 =>
                          cases assump_469
                          case intro assump_507 assump_508 =>
                            cases assump_467
                            case inl assump_513 =>
                              cases assump_513
                              case inl assump_515 =>
                                have assump_763 : p6 := by
                                  exact assump_371
                                let assump_521 := assump_507 assump_763
                                apply False.elim assump_521
                              case inr assump_516 =>
                                have assump_764 : p7 := by
                                  exact assump_17
                                let assump_527 := assump_516 assump_764
                                apply False.elim assump_527
                            case inr assump_514 =>
                              cases assump_514
                              case intro assump_531 assump_532 =>
                                cases assump_532
                                case intro assump_535 assump_536 =>
                                  have assump_765 : p6 := by
                                    exact assump_535
                                  let assump_546 := assump_507 assump_765
                                  apply False.elim assump_546
                  case inr assump_369 =>
                    cases assump_7
                    case intro assump_552 assump_553 =>
                      cases assump_552
                      case inl assump_554 =>
                        cases assump_553
                        case inl assump_558 =>
                          cases assump_558
                          case inl assump_560 =>
                            have assump_766 : (True ∧ p1) := by
                              apply And.intro
                              apply True.intro
                              exact assump_16
                            let assump_565 := assump_554 assump_766
                            apply False.elim assump_565
                          case inr assump_561 =>
                            have assump_767 : p7 := by
                              exact assump_17
                            let assump_571 := assump_561 assump_767
                            apply False.elim assump_571
                        case inr assump_559 =>
                          cases assump_559
                          case intro assump_575 assump_576 =>
                            cases assump_576
                            case intro assump_579 assump_580 =>
                              have assump_768 : (True ∧ p1) := by
                                apply And.intro
                                apply True.intro
                                exact assump_16
                              let assump_589 := assump_554 assump_768
                              apply False.elim assump_589
                      case inr assump_555 =>
                        cases assump_555
                        case intro assump_593 assump_594 =>
                          cases assump_553
                          case inl assump_599 =>
                            cases assump_599
                            case inl assump_601 =>
                              have assump_769 : p1 := by
                                exact assump_16
                              let assump_613 := assump_12 assump_769
                              apply False.elim assump_613
                            case inr assump_602 =>
                              have assump_770 : p7 := by
                                exact assump_17
                              let assump_619 := assump_602 assump_770
                              apply False.elim assump_619
                          case inr assump_600 =>
                            cases assump_600
                            case intro assump_623 assump_624 =>
                              cases assump_624
                              case intro assump_627 assump_628 =>
                                have assump_771 : p6 := by
                                  exact assump_627
                                let assump_638 := assump_593 assump_771
                                apply False.elim assump_638
                case inr assump_367 =>
                  cases assump_7
                  case intro assump_644 assump_645 =>
                    cases assump_644
                    case inl assump_646 =>
                      cases assump_645
                      case inl assump_650 =>
                        cases assump_650
                        case inl assump_652 =>
                          have assump_772 : (True ∧ p1) := by
                            apply And.intro
                            apply True.intro
                            exact assump_16
                          let assump_657 := assump_646 assump_772
                          apply False.elim assump_657
                        case inr assump_653 =>
                          have assump_773 : p7 := by
                            exact assump_17
                          let assump_663 := assump_653 assump_773
                          apply False.elim assump_663
                      case inr assump_651 =>
                        cases assump_651
                        case intro assump_667 assump_668 =>
                          cases assump_668
                          case intro assump_671 assump_672 =>
                            have assump_774 : (True ∧ p1) := by
                              apply And.intro
                              apply True.intro
                              exact assump_16
                            let assump_681 := assump_646 assump_774
                            apply False.elim assump_681
                    case inr assump_647 =>
                      cases assump_647
                      case intro assump_685 assump_686 =>
                        cases assump_645
                        case inl assump_691 =>
                          cases assump_691
                          case inl assump_693 =>
                            have assump_775 : (p5 → True) := by
                              intro assump_701
                              apply True.intro
                            let assump_700 := assump_367 assump_775
                            apply False.elim assump_700
                          case inr assump_694 =>
                            have assump_776 : p7 := by
                              exact assump_17
                            let assump_707 := assump_694 assump_776
                            apply False.elim assump_707
                        case inr assump_692 =>
                          cases assump_692
                          case intro assump_711 assump_712 =>
                            cases assump_712
                            case intro assump_715 assump_716 =>
                              have assump_777 : p6 := by
                                exact assump_715
                              let assump_726 := assump_685 assump_777
                              apply False.elim assump_726


variable (p1 p6 p7 p0 p5 : Prop)
theorem file35_28207 : (((((True ∨ p5) → (True → True)) ∨ ((p5 → False) ∨ (p5 ∧ p6))) ∧ (((p1 → False) → False) → ((p5 ∧ True) → (True ∨ True)))) ∨ ((((True ∨ False) ∧ (True ∨ p5)) ∨ ((p7 ∨ p1) ∧ (p0 ∧ p1))) → False)) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    apply True.intro


variable (p7 p6 p2 p4 : Prop)
theorem file35_28686 : (((((False → False) ∧ (p7 → False)) → ((False → False) ∨ (p4 → False))) → (((p2 ∨ p6) → False) ∧ ((p6 → p4) → False))) → False) := by
  intro assump_5
  have assump_45 : (((False → False) ∧ (p7 → False)) → ((False → False) ∨ (p4 → False))) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply Or.inl
      intro assump_16
      apply False.elim assump_16
  let assump_8 := assump_5 assump_45
  let assump_19 := And.right assump_8
  have assump_46 : (p6 → p4) := by
    intro assump_22
    have assump_47 : (((False → False) ∧ (p7 → False)) → ((False → False) ∨ (p4 → False))) := by
      intro assump_27
      cases assump_27
      case intro assump_28 assump_29 =>
        apply Or.inl
        intro assump_34
        apply False.elim assump_34
    let assump_26 := assump_5 assump_47
    let assump_37 := And.left assump_26
    have assump_48 : (p2 ∨ p6) := by
      apply Or.inr
      exact assump_22
    let assump_38 := assump_37 assump_48
    apply False.elim assump_38
  let assump_21 := assump_19 assump_46
  apply False.elim assump_21


variable (p1 p3 p5 p6 p7 p2 p0 p4 : Prop)
theorem file35_29837 : (((((False ∧ p1) ∧ (p3 → False)) ∧ ((p0 ∨ p2) → False)) ∧ (((True ∨ p4) ∧ (p0 → False)) ∨ ((p5 → p4) ∧ (p4 ∨ False)))) → ((((False ∧ p7) → (p1 → p3)) → ((p6 → False) ∧ (p6 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_11


variable (p7 p5 p4 p6 p3 p2 p0 p1 : Prop)
theorem file35_30404 : (((((p4 ∧ p1) ∧ (p3 → False)) → ((False ∧ p5) → False)) ∨ (((p5 ∨ p6) ∧ (True → p4)) ∨ ((p7 ∨ p3) ∨ (p3 → p7)))) ∨ ((((p1 ∨ False) → (p6 ∨ p4)) ∨ ((p0 ∨ p5) ∧ (p4 ∨ p3))) ∧ (((p2 ∨ p2) → (p5 → False)) → ((p7 ∧ p0) → (p0 → p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p7 p6 p3 p0 p4 : Prop)
theorem file35_30842 : (((((False ∨ p4) → (p7 → p0)) → False) ∨ (((p4 ∨ False) ∧ (p0 → False)) ∧ ((p3 → p0) → False))) → ((((p7 ∨ p6) → (True ∨ p0)) ∨ ((p4 ∧ p0) → False)) ∨ (((False → False) → False) ∨ ((p4 ∨ False) ∨ (p7 ∨ True))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          apply Or.inl
          apply Or.inl
          intro assump_25
          cases assump_25
          case inl assump_26 =>
            apply Or.inl
            apply True.intro
          case inr assump_27 =>
            apply Or.inl
            apply True.intro
        case inr assump_18 =>
          apply False.elim assump_18


variable (p6 p7 p3 p0 p4 p5 : Prop)
theorem file35_31916 : (((((p3 → False) → (False ∨ p6)) ∨ ((False → False) → False)) ∧ (((p0 → False) → (p0 ∨ True)) → False)) → ((((p5 → False) → (p0 → True)) ∧ ((p0 ∨ p4) ∨ (True ∨ p5))) ∧ (((p5 → False) → False) → ((p4 → False) → (p3 ∧ p7))))) := by
  intro assump_5
  apply And.intro
  apply And.intro
  intro assump_6
  intro assump_7
  apply True.intro
  cases assump_5
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      apply Or.inr
      apply Or.inl
      apply True.intro
    case inr assump_11 =>
      apply Or.inr
      apply Or.inl
      apply True.intro
  intro assump_20
  intro assump_21
  apply And.intro
  cases assump_5
  case intro assump_26 assump_27 =>
    cases assump_26
    case inl assump_28 =>
      have assump_82 : ((p0 → False) → (p0 ∨ True)) := by
        intro assump_35
        apply Or.inr
        apply True.intro
      let assump_34 := assump_27 assump_82
      apply False.elim assump_34
    case inr assump_29 =>
      have assump_83 : ((p0 → False) → (p0 ∨ True)) := by
        intro assump_46
        apply Or.inr
        apply True.intro
      let assump_45 := assump_27 assump_83
      apply False.elim assump_45
  cases assump_5
  case intro assump_56 assump_57 =>
    cases assump_56
    case inl assump_58 =>
      have assump_84 : ((p0 → False) → (p0 ∨ True)) := by
        intro assump_65
        apply Or.inr
        apply True.intro
      let assump_64 := assump_57 assump_84
      apply False.elim assump_64
    case inr assump_59 =>
      have assump_85 : ((p0 → False) → (p0 ∨ True)) := by
        intro assump_76
        apply Or.inr
        apply True.intro
      let assump_75 := assump_57 assump_85
      apply False.elim assump_75


variable (p5 p1 p6 p7 : Prop)
theorem file35_33670 : (((((False → p7) → False) → False) ∨ (((True ∨ p1) → False) → False)) ∨ ((((p5 → False) ∨ (False ∧ p1)) ∧ ((False → p6) → False)) ∧ (((p6 → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → p7) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p0 p3 p7 p4 p5 p2 p6 : Prop)
theorem file35_34108 : (((((p0 ∧ p7) → (p2 ∧ p0)) ∨ ((p4 → False) → False)) ∧ (((True → False) ∧ (p3 ∨ p2)) ∧ ((p0 ∧ p3) → False))) → ((((p5 → False) ∧ (p4 → False)) ∧ ((p2 ∨ p4) ∧ (p3 ∨ p0))) ∨ (((p2 → False) ∧ (True ∧ p3)) ∧ ((p1 ∧ p6) ∨ (p6 ∨ p3))))) := by
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
          case inl assump_14 =>
            apply Or.inr
            apply And.intro
            apply And.intro
            intro assump_40
            have assump_174 : True := by
              apply True.intro
            let assump_46 := assump_10 assump_174
            apply False.elim assump_46
            apply And.intro
            apply True.intro
            exact assump_14
            apply Or.inr
            apply Or.inr
            exact assump_14
          case inr assump_15 =>
            have assump_175 : True := by
              apply True.intro
            let assump_86 := assump_10 assump_175
            apply False.elim assump_86
    case inr assump_5 =>
      cases assump_3
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_95
          case inl assump_98 =>
            apply Or.inr
            apply And.intro
            apply And.intro
            intro assump_124
            have assump_176 : True := by
              apply True.intro
            let assump_130 := assump_94 assump_176
            apply False.elim assump_130
            apply And.intro
            apply True.intro
            exact assump_98
            apply Or.inr
            apply Or.inr
            exact assump_98
          case inr assump_99 =>
            have assump_177 : True := by
              apply True.intro
            let assump_170 := assump_94 assump_177
            apply False.elim assump_170


variable (p7 p5 p2 p3 p4 : Prop)
theorem file35_36163 : (((((p5 → False) → (p7 → False)) → ((p4 → p2) → (False → False))) → False) → ((((p5 ∧ False) ∨ (p3 ∧ p5)) → ((p3 → False) → False)) → (((p5 ∨ True) → False) ∧ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    have assump_52 : (((p5 → False) → (p7 → False)) → ((p4 → p2) → (False → False))) := by
      intro assump_13
      intro assump_14
      intro assump_15
      apply False.elim assump_15
    let assump_12 := assump_1 assump_52
    apply False.elim assump_12
  case inr assump_5 =>
    have assump_53 : (((p5 → False) → (p7 → False)) → ((p4 → p2) → (False → False))) := by
      intro assump_28
      intro assump_29
      intro assump_30
      apply False.elim assump_30
    let assump_27 := assump_1 assump_53
    apply False.elim assump_27
  intro assump_36
  have assump_54 : (((p5 → False) → (p7 → False)) → ((p4 → p2) → (False → False))) := by
    intro assump_44
    intro assump_45
    intro assump_46
    apply False.elim assump_46
  let assump_43 := assump_1 assump_54
  apply False.elim assump_43


variable (p4 p2 p0 p3 p1 p6 p7 : Prop)
theorem file35_37336 : ((((((p0 → p1) → (p3 → p2)) → ((p1 ∧ p4) ∧ (p6 → p6))) → False) ∧ ((((p1 → p4) → (p2 → p4)) ∨ ((p3 → p2) → False)) ∧ (((p7 → False) → (True → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_30 : ((p7 → False) → (True → True)) := by
          intro assump_15
          intro assump_16
          apply True.intro
        let assump_14 := assump_7 assump_30
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_31 : ((p7 → False) → (True → True)) := by
          intro assump_25
          intro assump_26
          apply True.intro
        let assump_24 := assump_7 assump_31
        apply False.elim assump_24


variable (p3 p0 p2 p7 p6 : Prop)
theorem file35_38206 : ((((((p7 → False) ∧ (p6 ∨ p6)) → ((p6 ∨ p2) → (False → False))) ∨ (((p0 ∧ p3) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p7 → False) ∧ (p6 ∨ p6)) → ((p6 ∨ p2) → (False → False))) ∨ (((p0 ∧ p3) → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p6 p1 p2 : Prop)
theorem file35_38687 : ((((((p1 → p5) → False) → False) → (((p6 ∧ p5) ∧ (False ∧ False)) → ((p2 → p6) → (p5 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p1 → p5) → False) → False) → (((p6 ∧ p5) ∧ (False ∧ False)) → ((p2 → p6) → (p5 → True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p7 p4 p6 p2 : Prop)
theorem file35_39162 : ((((((p4 ∨ p1) → (False → False)) → ((p7 → p2) → (True ∨ True))) ∨ (((p1 → p6) → False) → ((p1 ∨ p7) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p4 ∨ p1) → (False → False)) → ((p7 → p2) → (True ∨ True))) ∨ (((p1 → p6) → False) → ((p1 ∨ p7) ∨ (True → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p4 p6 p7 p1 p0 : Prop)
theorem file35_39686 : ((((((p5 ∨ p7) ∧ (p4 → p1)) ∨ ((p7 ∧ True) → (p7 ∨ p5))) ∨ (((p6 → p4) ∨ (p6 ∨ p0)) ∨ ((p6 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p5 ∨ p7) ∧ (p4 → p1)) ∨ ((p7 ∧ True) → (p7 ∨ p5))) ∨ (((p6 → p4) ∨ (p6 ∨ p0)) ∨ ((p6 → False) → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      exact assump_6
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p7 p3 p0 p4 p2 : Prop)
theorem file35_40245 : (((((False ∧ p7) ∧ (True → p5)) → ((p2 ∧ p5) ∨ (True ∨ p4))) → (((p2 → p3) ∧ (p0 → p2)) ∧ ((p3 ∨ True) → False))) → ((((p2 → False) → (p4 ∨ p0)) → ((p2 ∧ p3) ∧ (p2 → p3))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_23 : (((False ∧ p7) ∧ (True → p5)) → ((p2 ∧ p5) ∨ (True ∨ p4))) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_7 := assump_1 assump_23
  let assump_15 := And.right assump_7
  have assump_24 : (p3 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_19 := assump_15 assump_24
  apply False.elim assump_19


variable (p5 p3 p0 : Prop)
theorem file35_40991 : (((((p3 → False) ∧ (p5 ∨ p5)) ∨ ((p0 → False) ∧ (False ∨ p5))) ∧ (((True ∨ True) ∨ (p0 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          have assump_44 : ((True ∨ True) ∨ (p0 → False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_16 := assump_3 assump_44
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_45 : ((True ∨ True) ∨ (p0 → False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_24 := assump_3 assump_45
          apply False.elim assump_24
    case inr assump_5 =>
      cases assump_5
      case intro assump_28 assump_29 =>
        cases assump_29
        case inl assump_32 =>
          apply False.elim assump_32
        case inr assump_33 =>
          have assump_46 : ((True ∨ True) ∨ (p0 → False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_40 := assump_3 assump_46
          apply False.elim assump_40


variable (p2 p7 p1 p0 p6 p4 p5 p3 : Prop)
theorem file35_42318 : (((((p1 ∨ False) → False) ∧ ((p1 ∧ p1) ∧ (p3 ∧ p7))) → (((p6 ∧ p1) ∧ (p6 ∨ p2)) ∧ ((p5 ∧ True) → False))) ∨ ((((True → p0) ∨ (p2 ∧ p2)) ∨ ((p4 ∨ p0) ∧ (p4 → p2))) ∨ (((False → False) ∨ (p3 → p4)) ∧ ((p6 ∧ p5) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          have assump_105 : (p1 ∨ False) := by
            apply Or.inl
            exact assump_9
          let assump_24 := assump_2 assump_105
          apply False.elim assump_24
  cases assump_1
  case intro assump_28 assump_29 =>
    cases assump_29
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_33
        case intro assump_40 assump_41 =>
          exact assump_35
  cases assump_1
  case intro assump_46 assump_47 =>
    cases assump_47
    case intro assump_50 assump_51 =>
      cases assump_50
      case intro assump_52 assump_53 =>
        cases assump_51
        case intro assump_58 assump_59 =>
          have assump_106 : (p1 ∨ False) := by
            apply Or.inl
            exact assump_53
          let assump_68 := assump_46 assump_106
          apply False.elim assump_68
  intro assump_72
  cases assump_72
  case intro assump_73 assump_74 =>
    cases assump_1
    case intro assump_79 assump_80 =>
      cases assump_80
      case intro assump_83 assump_84 =>
        cases assump_83
        case intro assump_85 assump_86 =>
          cases assump_84
          case intro assump_91 assump_92 =>
            have assump_107 : (p1 ∨ False) := by
              apply Or.inl
              exact assump_86
            let assump_101 := assump_79 assump_107
            apply False.elim assump_101


variable (p7 p1 p2 p3 p6 p5 : Prop)
theorem file35_44317 : (((((p1 ∧ p7) → (p3 ∨ p7)) → False) → False) ∨ ((((p2 ∨ p5) → False) → ((p6 → p3) ∧ (p5 ∧ p6))) → False)) := by
  apply Or.inl
  intro assump_5
  have assump_19 : ((p1 ∧ p7) → (p3 ∨ p7)) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply Or.inr
      exact assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p6 p4 p0 p5 p7 p1 p2 p3 : Prop)
theorem file35_44758 : ((((((False ∨ p5) ∧ (p7 ∧ p2)) ∨ ((p0 ∧ p2) ∨ (True ∧ p2))) → (((p2 ∨ p1) ∧ (p2 → p4)) → ((p3 → p3) ∨ (p7 ∧ p6)))) → False) → False) := by
  intro assump_35
  have assump_134 : ((((False ∨ p5) ∧ (p7 ∧ p2)) ∨ ((p0 ∧ p2) ∨ (True ∧ p2))) → (((p2 ∨ p1) ∧ (p2 → p4)) → ((p3 → p3) ∨ (p7 ∧ p6)))) := by
    intro assump_39
    intro assump_40
    cases assump_40
    case intro assump_41 assump_42 =>
      cases assump_41
      case inl assump_43 =>
        cases assump_39
        case inl assump_49 =>
          cases assump_49
          case intro assump_51 assump_52 =>
            cases assump_51
            case inl assump_53 =>
              apply False.elim assump_53
            case inr assump_54 =>
              cases assump_52
              case intro assump_59 assump_60 =>
                apply Or.inl
                intro assump_65
                exact assump_65
        case inr assump_50 =>
          cases assump_50
          case inl assump_68 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              apply Or.inl
              intro assump_76
              exact assump_76
          case inr assump_69 =>
            cases assump_69
            case intro assump_79 assump_80 =>
              apply Or.inl
              intro assump_85
              exact assump_85
      case inr assump_44 =>
        cases assump_39
        case inl assump_92 =>
          cases assump_92
          case intro assump_94 assump_95 =>
            cases assump_94
            case inl assump_96 =>
              apply False.elim assump_96
            case inr assump_97 =>
              cases assump_95
              case intro assump_102 assump_103 =>
                apply Or.inl
                intro assump_108
                exact assump_108
        case inr assump_93 =>
          cases assump_93
          case inl assump_111 =>
            cases assump_111
            case intro assump_113 assump_114 =>
              apply Or.inl
              intro assump_119
              exact assump_119
          case inr assump_112 =>
            cases assump_112
            case intro assump_122 assump_123 =>
              apply Or.inl
              intro assump_128
              exact assump_128
  let assump_38 := assump_35 assump_134
  apply False.elim assump_38


variable (p2 p1 p3 p0 p5 p7 p6 : Prop)
theorem file35_47126 : (((((False ∧ True) ∧ (p6 ∨ p0)) → False) ∨ (((p5 → p3) → False) ∧ ((True ∨ True) → (p1 ∨ p6)))) ∨ ((((True → False) ∨ (p3 ∨ p6)) → False) → (((p2 ∨ False) → (p7 → p3)) ∧ ((p6 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p1 p0 p5 p4 p2 p6 p3 : Prop)
theorem file35_47576 : (((((p1 → True) ∨ (p1 → p1)) ∨ ((p6 → False) ∧ (p4 ∨ p6))) ∨ (((False ∧ False) → (p3 ∨ p0)) ∧ ((p4 → False) ∨ (p2 → p3)))) ∨ ((((p3 → True) ∧ (p5 ∧ False)) ∨ ((False → p4) ∧ (p6 ∧ p2))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p3 p5 p4 p2 p6 p0 p7 : Prop)
theorem file35_47937 : ((((((p7 → False) ∧ (p5 ∧ True)) ∧ ((p4 → p6) ∨ (True → False))) → (((True → False) → False) ∧ ((True → False) ∨ (p3 → False)))) ∧ ((((p2 ∧ False) ∧ (True ∨ p0)) → False) → (((p3 ∧ p5) ∧ (p0 → p4)) ∧ ((True ∨ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((p2 ∧ False) ∧ (True ∨ p0)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_28
    let assump_18 := And.right assump_8
    have assump_29 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_24 := assump_18 assump_29
    apply False.elim assump_24


variable (p2 p3 p5 p1 : Prop)
theorem file35_48788 : (((((p5 ∧ False) → False) → False) → False) ∨ ((((p2 ∧ p3) ∨ (True ∧ p1)) ∧ ((False ∨ p3) ∨ (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p5 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p2 p4 p3 p0 p5 p7 : Prop)
theorem file35_49225 : (((((p4 ∨ p5) → False) → False) ∧ (((p2 ∧ p7) ∧ (p2 ∨ p1)) ∧ ((True ∨ p2) → False))) → ((((p4 → False) ∨ (p0 ∨ p3)) → ((p0 → False) → False)) → (((p4 → False) ∧ (p7 → False)) ∧ ((p1 ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case inl assump_22 =>
            have assump_118 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_28 := assump_13 assump_118
            apply False.elim assump_28
          case inr assump_23 =>
            have assump_119 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_36 := assump_13 assump_119
            apply False.elim assump_36
  intro assump_40
  cases assump_1
  case intro assump_45 assump_46 =>
    cases assump_46
    case intro assump_49 assump_50 =>
      cases assump_49
      case intro assump_51 assump_52 =>
        cases assump_51
        case intro assump_53 assump_54 =>
          cases assump_52
          case inl assump_59 =>
            have assump_120 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_65 := assump_50 assump_120
            apply False.elim assump_65
          case inr assump_60 =>
            have assump_121 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_73 := assump_50 assump_121
            apply False.elim assump_73
  intro assump_77
  cases assump_77
  case intro assump_78 assump_79 =>
    cases assump_1
    case intro assump_86 assump_87 =>
      cases assump_87
      case intro assump_90 assump_91 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          cases assump_92
          case intro assump_94 assump_95 =>
            cases assump_93
            case inl assump_100 =>
              have assump_122 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_106 := assump_91 assump_122
              apply False.elim assump_106
            case inr assump_101 =>
              have assump_123 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_114 := assump_91 assump_123
              apply False.elim assump_114


variable (p4 p0 p1 p2 p7 p3 p6 p5 : Prop)
theorem file35_51876 : (((((True → p6) ∨ (p6 ∧ p1)) ∨ ((p3 → False) ∨ (p4 → False))) ∧ (((True ∧ p3) → False) ∧ ((p0 ∧ p3) ∧ (True ∨ True)))) → ((((p2 ∨ False) → (p0 ∨ p1)) ∧ ((True → p0) → False)) ∧ (((p3 ∧ p7) → False) ∨ ((p5 ∨ p0) → (p0 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_8
          case intro assump_15 assump_16 =>
            cases assump_16
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                cases assump_20
                case inl assump_27 =>
                  apply Or.inl
                  exact assump_21
                case inr assump_28 =>
                  apply Or.inl
                  exact assump_21
        case inr assump_12 =>
          cases assump_12
          case intro assump_33 assump_34 =>
            cases assump_8
            case intro assump_39 assump_40 =>
              cases assump_40
              case intro assump_43 assump_44 =>
                cases assump_43
                case intro assump_45 assump_46 =>
                  cases assump_44
                  case inl assump_51 =>
                    apply Or.inl
                    exact assump_45
                  case inr assump_52 =>
                    apply Or.inl
                    exact assump_45
      case inr assump_10 =>
        cases assump_10
        case inl assump_57 =>
          cases assump_8
          case intro assump_61 assump_62 =>
            cases assump_62
            case intro assump_65 assump_66 =>
              cases assump_65
              case intro assump_67 assump_68 =>
                cases assump_66
                case inl assump_73 =>
                  apply Or.inl
                  exact assump_67
                case inr assump_74 =>
                  apply Or.inl
                  exact assump_67
        case inr assump_58 =>
          cases assump_8
          case intro assump_81 assump_82 =>
            cases assump_82
            case intro assump_85 assump_86 =>
              cases assump_85
              case intro assump_87 assump_88 =>
                cases assump_86
                case inl assump_93 =>
                  apply Or.inl
                  exact assump_87
                case inr assump_94 =>
                  apply Or.inl
                  exact assump_87
  case inr assump_4 =>
    apply False.elim assump_4
  intro assump_101
  cases assump_1
  case intro assump_104 assump_105 =>
    cases assump_104
    case inl assump_106 =>
      cases assump_106
      case inl assump_108 =>
        cases assump_105
        case intro assump_112 assump_113 =>
          cases assump_113
          case intro assump_116 assump_117 =>
            cases assump_116
            case intro assump_118 assump_119 =>
              cases assump_117
              case inl assump_124 =>
                have assump_456 : (True ∧ p3) := by
                  apply And.intro
                  apply True.intro
                  exact assump_119
                let assump_130 := assump_112 assump_456
                apply False.elim assump_130
              case inr assump_125 =>
                have assump_457 : (True ∧ p3) := by
                  apply And.intro
                  apply True.intro
                  exact assump_119
                let assump_138 := assump_112 assump_457
                apply False.elim assump_138
      case inr assump_109 =>
        cases assump_109
        case intro assump_142 assump_143 =>
          cases assump_105
          case intro assump_148 assump_149 =>
            cases assump_149
            case intro assump_152 assump_153 =>
              cases assump_152
              case intro assump_154 assump_155 =>
                cases assump_153
                case inl assump_160 =>
                  have assump_458 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_155
                  let assump_166 := assump_148 assump_458
                  apply False.elim assump_166
                case inr assump_161 =>
                  have assump_459 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_155
                  let assump_174 := assump_148 assump_459
                  apply False.elim assump_174
    case inr assump_107 =>
      cases assump_107
      case inl assump_178 =>
        cases assump_105
        case intro assump_182 assump_183 =>
          cases assump_183
          case intro assump_186 assump_187 =>
            cases assump_186
            case intro assump_188 assump_189 =>
              cases assump_187
              case inl assump_194 =>
                have assump_460 : (True ∧ p3) := by
                  apply And.intro
                  apply True.intro
                  exact assump_189
                let assump_200 := assump_182 assump_460
                apply False.elim assump_200
              case inr assump_195 =>
                have assump_461 : (True ∧ p3) := by
                  apply And.intro
                  apply True.intro
                  exact assump_189
                let assump_208 := assump_182 assump_461
                apply False.elim assump_208
      case inr assump_179 =>
        cases assump_105
        case intro assump_214 assump_215 =>
          cases assump_215
          case intro assump_218 assump_219 =>
            cases assump_218
            case intro assump_220 assump_221 =>
              cases assump_219
              case inl assump_226 =>
                have assump_462 : (True ∧ p3) := by
                  apply And.intro
                  apply True.intro
                  exact assump_221
                let assump_232 := assump_214 assump_462
                apply False.elim assump_232
              case inr assump_227 =>
                have assump_463 : (True ∧ p3) := by
                  apply And.intro
                  apply True.intro
                  exact assump_221
                let assump_240 := assump_214 assump_463
                apply False.elim assump_240
  cases assump_1
  case intro assump_244 assump_245 =>
    cases assump_244
    case inl assump_246 =>
      cases assump_246
      case inl assump_248 =>
        cases assump_245
        case intro assump_252 assump_253 =>
          cases assump_253
          case intro assump_256 assump_257 =>
            cases assump_256
            case intro assump_258 assump_259 =>
              cases assump_257
              case inl assump_264 =>
                apply Or.inl
                intro assump_268
                cases assump_268
                case intro assump_269 assump_270 =>
                  have assump_464 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_269
                  let assump_279 := assump_252 assump_464
                  apply False.elim assump_279
              case inr assump_265 =>
                apply Or.inl
                intro assump_285
                cases assump_285
                case intro assump_286 assump_287 =>
                  have assump_465 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_286
                  let assump_296 := assump_252 assump_465
                  apply False.elim assump_296
      case inr assump_249 =>
        cases assump_249
        case intro assump_300 assump_301 =>
          cases assump_245
          case intro assump_306 assump_307 =>
            cases assump_307
            case intro assump_310 assump_311 =>
              cases assump_310
              case intro assump_312 assump_313 =>
                cases assump_311
                case inl assump_318 =>
                  apply Or.inl
                  intro assump_322
                  cases assump_322
                  case intro assump_323 assump_324 =>
                    have assump_466 : (True ∧ p3) := by
                      apply And.intro
                      apply True.intro
                      exact assump_323
                    let assump_333 := assump_306 assump_466
                    apply False.elim assump_333
                case inr assump_319 =>
                  apply Or.inl
                  intro assump_339
                  cases assump_339
                  case intro assump_340 assump_341 =>
                    have assump_467 : (True ∧ p3) := by
                      apply And.intro
                      apply True.intro
                      exact assump_340
                    let assump_350 := assump_306 assump_467
                    apply False.elim assump_350
    case inr assump_247 =>
      cases assump_247
      case inl assump_354 =>
        cases assump_245
        case intro assump_358 assump_359 =>
          cases assump_359
          case intro assump_362 assump_363 =>
            cases assump_362
            case intro assump_364 assump_365 =>
              cases assump_363
              case inl assump_370 =>
                apply Or.inl
                intro assump_374
                cases assump_374
                case intro assump_375 assump_376 =>
                  have assump_468 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_375
                  let assump_385 := assump_358 assump_468
                  apply False.elim assump_385
              case inr assump_371 =>
                apply Or.inl
                intro assump_391
                cases assump_391
                case intro assump_392 assump_393 =>
                  have assump_469 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_392
                  let assump_402 := assump_358 assump_469
                  apply False.elim assump_402
      case inr assump_355 =>
        cases assump_245
        case intro assump_408 assump_409 =>
          cases assump_409
          case intro assump_412 assump_413 =>
            cases assump_412
            case intro assump_414 assump_415 =>
              cases assump_413
              case inl assump_420 =>
                apply Or.inl
                intro assump_424
                cases assump_424
                case intro assump_425 assump_426 =>
                  have assump_470 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_425
                  let assump_435 := assump_408 assump_470
                  apply False.elim assump_435
              case inr assump_421 =>
                apply Or.inl
                intro assump_441
                cases assump_441
                case intro assump_442 assump_443 =>
                  have assump_471 : (True ∧ p3) := by
                    apply And.intro
                    apply True.intro
                    exact assump_442
                  let assump_452 := assump_408 assump_471
                  apply False.elim assump_452


variable (p1 p4 p3 p0 p2 : Prop)
theorem file35_63363 : ((((((p4 → False) ∨ (False → False)) ∧ ((p3 ∨ False) → False)) → (((p0 → p0) ∧ (p3 → False)) ∨ ((p3 → p1) ∧ (False → p2)))) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p4 → False) ∨ (False → False)) ∧ ((p3 ∨ False) → False)) → (((p0 → p0) ∧ (p3 → False)) ∨ ((p3 → p1) ∧ (False → p2)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply And.intro
        intro assump_14
        exact assump_14
        intro assump_17
        have assump_44 : (p3 ∨ False) := by
          apply Or.inl
          exact assump_17
        let assump_21 := assump_7 assump_44
        apply False.elim assump_21
      case inr assump_9 =>
        apply Or.inl
        apply And.intro
        intro assump_29
        exact assump_29
        intro assump_32
        have assump_45 : (p3 ∨ False) := by
          apply Or.inl
          exact assump_32
        let assump_36 := assump_7 assump_45
        apply False.elim assump_36
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p7 p2 p3 p4 p6 : Prop)
theorem file35_64524 : ((((((p2 → p7) → False) → ((False → p4) ∨ (p3 → False))) ∨ (((p4 ∨ p3) → (p6 ∨ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → p7) → False) → ((False → p4) ∨ (p3 → False))) ∨ (((p4 ∨ p3) → (p6 ∨ True)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p3 p6 p7 p0 : Prop)
theorem file35_65004 : (((((True ∨ p3) → False) ∧ ((p2 ∧ p2) ∧ (True ∧ p2))) ∧ (((p0 ∨ p3) → (p7 ∧ True)) ∨ ((False ∨ p2) → (p6 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_3
            case inl assump_22 =>
              have assump_45 : (True ∨ p3) := by
                apply Or.inl
                apply True.intro
              let assump_30 := assump_4 assump_45
              apply False.elim assump_30
            case inr assump_23 =>
              have assump_46 : (True ∨ p3) := by
                apply Or.inl
                apply True.intro
              let assump_41 := assump_4 assump_46
              apply False.elim assump_41


variable (p0 p4 p6 p3 p7 p5 p2 p1 : Prop)
theorem file35_66017 : (((((p6 → False) → (p7 ∨ p5)) ∧ ((False ∧ p5) ∧ (p7 → p5))) → False) ∨ ((((p7 → p5) ∨ (False ∨ p0)) ∧ ((p7 ∧ p2) ∧ (p1 ∨ p1))) ∧ (((p4 → False) ∨ (p3 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8


variable (p7 p6 p4 p1 p0 p2 p5 p3 : Prop)
theorem file35_66491 : (((((p7 → False) ∧ (True → p2)) ∨ ((p1 ∨ p2) → (False ∧ p4))) ∨ (((p1 → p5) ∨ (p3 ∨ p7)) ∨ ((p7 ∧ True) ∨ (p6 → p5)))) → ((((False ∨ p6) → False) ∨ ((p5 ∧ p1) ∨ (p5 → False))) → (((False ∧ p2) → (p4 ∨ p5)) ∨ ((False ∨ p0) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply Or.inl
          intro assump_17
          cases assump_17
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
      case inr assump_10 =>
        apply Or.inl
        intro assump_24
        cases assump_24
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
    case inr assump_8 =>
      cases assump_8
      case inl assump_29 =>
        cases assump_29
        case inl assump_31 =>
          apply Or.inl
          intro assump_35
          cases assump_35
          case intro assump_36 assump_37 =>
            apply False.elim assump_36
        case inr assump_32 =>
          cases assump_32
          case inl assump_40 =>
            apply Or.inl
            intro assump_44
            cases assump_44
            case intro assump_45 assump_46 =>
              apply False.elim assump_45
          case inr assump_41 =>
            apply Or.inl
            intro assump_51
            cases assump_51
            case intro assump_52 assump_53 =>
              apply False.elim assump_52
      case inr assump_30 =>
        cases assump_30
        case inl assump_56 =>
          cases assump_56
          case intro assump_58 assump_59 =>
            apply Or.inl
            intro assump_64
            cases assump_64
            case intro assump_65 assump_66 =>
              apply False.elim assump_65
        case inr assump_57 =>
          apply Or.inl
          intro assump_71
          cases assump_71
          case intro assump_72 assump_73 =>
            apply False.elim assump_72
  case inr assump_4 =>
    cases assump_4
    case inl assump_76 =>
      cases assump_76
      case intro assump_78 assump_79 =>
        cases assump_1
        case inl assump_84 =>
          cases assump_84
          case inl assump_86 =>
            cases assump_86
            case intro assump_88 assump_89 =>
              apply Or.inl
              intro assump_94
              cases assump_94
              case intro assump_95 assump_96 =>
                apply False.elim assump_95
          case inr assump_87 =>
            apply Or.inl
            intro assump_101
            cases assump_101
            case intro assump_102 assump_103 =>
              apply False.elim assump_102
        case inr assump_85 =>
          cases assump_85
          case inl assump_106 =>
            cases assump_106
            case inl assump_108 =>
              apply Or.inl
              intro assump_112
              cases assump_112
              case intro assump_113 assump_114 =>
                apply False.elim assump_113
            case inr assump_109 =>
              cases assump_109
              case inl assump_117 =>
                apply Or.inl
                intro assump_121
                cases assump_121
                case intro assump_122 assump_123 =>
                  apply False.elim assump_122
              case inr assump_118 =>
                apply Or.inl
                intro assump_128
                cases assump_128
                case intro assump_129 assump_130 =>
                  apply False.elim assump_129
          case inr assump_107 =>
            cases assump_107
            case inl assump_133 =>
              cases assump_133
              case intro assump_135 assump_136 =>
                apply Or.inl
                intro assump_141
                cases assump_141
                case intro assump_142 assump_143 =>
                  apply False.elim assump_142
            case inr assump_134 =>
              apply Or.inl
              intro assump_148
              cases assump_148
              case intro assump_149 assump_150 =>
                apply False.elim assump_149
    case inr assump_77 =>
      cases assump_1
      case inl assump_155 =>
        cases assump_155
        case inl assump_157 =>
          cases assump_157
          case intro assump_159 assump_160 =>
            apply Or.inl
            intro assump_165
            cases assump_165
            case intro assump_166 assump_167 =>
              apply False.elim assump_166
        case inr assump_158 =>
          apply Or.inl
          intro assump_172
          cases assump_172
          case intro assump_173 assump_174 =>
            apply False.elim assump_173
      case inr assump_156 =>
        cases assump_156
        case inl assump_177 =>
          cases assump_177
          case inl assump_179 =>
            apply Or.inl
            intro assump_183
            cases assump_183
            case intro assump_184 assump_185 =>
              apply False.elim assump_184
          case inr assump_180 =>
            cases assump_180
            case inl assump_188 =>
              apply Or.inl
              intro assump_192
              cases assump_192
              case intro assump_193 assump_194 =>
                apply False.elim assump_193
            case inr assump_189 =>
              apply Or.inl
              intro assump_199
              cases assump_199
              case intro assump_200 assump_201 =>
                apply False.elim assump_200
        case inr assump_178 =>
          cases assump_178
          case inl assump_204 =>
            cases assump_204
            case intro assump_206 assump_207 =>
              apply Or.inl
              intro assump_212
              cases assump_212
              case intro assump_213 assump_214 =>
                apply False.elim assump_213
          case inr assump_205 =>
            apply Or.inl
            intro assump_219
            cases assump_219
            case intro assump_220 assump_221 =>
              apply False.elim assump_220


variable (p0 p6 p7 p3 p1 : Prop)
theorem file35_72697 : ((((((p3 → False) → False) → ((p0 ∨ True) ∨ (False → False))) ∨ (((p6 ∨ False) → (p7 ∨ p1)) → False)) → False) → False) := by
  intro assump_7
  have assump_17 : ((((p3 → False) → False) → ((p0 ∨ True) ∨ (False → False))) ∨ (((p6 ∨ False) → (p7 ∨ p1)) → False)) := by
    apply Or.inl
    intro assump_11
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_10 := assump_7 assump_17
  apply False.elim assump_10


variable (p7 p4 p0 p6 p5 p2 p1 p3 : Prop)
theorem file35_73190 : (((((p6 → False) → False) → ((False → p3) → False)) → (((p0 ∨ p2) → (p0 → p2)) ∨ ((p4 ∨ p3) → (p2 → p5)))) → ((((p0 → False) → (p6 ∨ True)) ∨ ((p0 → False) ∧ (p4 → False))) ∨ (((p2 ∧ p7) → False) ∨ ((False ∨ False) → (p0 → p1))))) := by
  intro assump_13
  apply Or.inl
  apply Or.inl
  intro assump_16
  apply Or.inr
  apply True.intro


variable (p3 p7 p5 p1 p2 p0 : Prop)
theorem file35_73587 : (((((p7 ∧ p7) → (p1 ∧ p5)) → False) → (((True ∨ p2) ∨ (p2 → p2)) ∨ ((False → False) → False))) ∧ ((((p0 → p5) ∨ (False ∨ p1)) → False) → (((p3 ∨ p7) → (p7 ∧ p2)) → ((False ∧ p7) → (True ∨ p3))))) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    apply False.elim assump_7


variable (p0 p2 p4 : Prop)
theorem file35_74071 : (((((p2 ∧ p4) → (p0 ∨ True)) ∧ ((p2 → False) → (False → p4))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p2 ∧ p4) → (p0 ∨ True)) ∧ ((p2 → False) → (False → p4))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      apply True.intro
    intro assump_12
    intro assump_13
    apply False.elim assump_13
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p4 p3 p2 p5 p0 : Prop)
theorem file35_74591 : (((((True ∧ p0) → False) ∧ ((p4 ∧ p3) → False)) ∧ (((p6 ∨ True) ∨ (False ∧ True)) → False)) → ((((True → False) ∨ (p5 → False)) → ((p2 → True) → (p3 ∧ False))) ∧ (((p3 → False) ∧ (p0 ∧ p6)) ∨ ((False → p4) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_102 : ((p6 ∨ True) ∨ (False ∧ True)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_20 := assump_11 assump_102
        apply False.elim assump_20
  case inr assump_7 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        have assump_103 : ((p6 ∨ True) ∨ (False ∧ True)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_36 := assump_27 assump_103
        apply False.elim assump_36
  cases assump_2
  case inl assump_42 =>
    cases assump_1
    case intro assump_46 assump_47 =>
      cases assump_46
      case intro assump_48 assump_49 =>
        have assump_104 : ((p6 ∨ True) ∨ (False ∧ True)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_56 := assump_47 assump_104
        apply False.elim assump_56
  case inr assump_43 =>
    cases assump_1
    case intro assump_62 assump_63 =>
      cases assump_62
      case intro assump_64 assump_65 =>
        have assump_105 : ((p6 ∨ True) ∨ (False ∧ True)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_72 := assump_63 assump_105
        apply False.elim assump_72
  cases assump_1
  case intro assump_76 assump_77 =>
    cases assump_76
    case intro assump_78 assump_79 =>
      apply Or.inr
      intro assump_94
      have assump_106 : ((p6 ∨ True) ∨ (False ∧ True)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_98 := assump_77 assump_106
      apply False.elim assump_98


variable (p1 p6 p4 p5 : Prop)
theorem file35_76785 : ((((((p5 → False) ∨ (False ∧ p4)) → False) ∨ (((p5 ∧ p1) → False) ∨ ((p1 → False) → False))) ∧ ((((p4 → p6) → (True → False)) → False) ∧ (((True ∨ p1) → (p6 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_50 : ((True ∨ p1) → (p6 → True)) := by
          intro assump_15
          intro assump_16
          apply True.intro
        let assump_14 := assump_9 assump_50
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_20 =>
        cases assump_3
        case intro assump_24 assump_25 =>
          have assump_51 : ((True ∨ p1) → (p6 → True)) := by
            intro assump_31
            intro assump_32
            apply True.intro
          let assump_30 := assump_25 assump_51
          apply False.elim assump_30
      case inr assump_21 =>
        cases assump_3
        case intro assump_38 assump_39 =>
          have assump_52 : ((True ∨ p1) → (p6 → True)) := by
            intro assump_45
            intro assump_46
            apply True.intro
          let assump_44 := assump_39 assump_52
          apply False.elim assump_44


variable (p7 p3 p4 p5 p2 p1 p6 p0 : Prop)
theorem file35_78123 : (((((p2 → False) → (p7 ∧ p4)) ∧ ((p7 → False) ∧ (p7 → True))) ∧ (((p3 → p1) → (p5 → p0)) ∧ ((p7 ∧ p5) → False))) → ((((p6 → p7) → False) → ((p5 → p6) → False)) → (((p6 → p6) ∨ (p2 → True)) ∨ ((p1 ∧ p1) ∨ (p4 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_6
        case intro assump_17 assump_18 =>
          apply Or.inl
          apply Or.inl
          intro assump_23
          exact assump_23


variable (p6 p0 p1 p7 p5 p4 : Prop)
theorem file35_78771 : ((((((True ∧ p7) → False) ∨ ((p5 → False) → (p6 ∧ p0))) → (((p0 → False) ∧ (False ∧ p4)) → ((p4 ∧ True) → (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True ∧ p7) → False) ∨ ((p5 → False) → (p6 ∧ p0))) → (((p0 → False) ∧ (False ∧ p4)) → ((p4 ∧ True) → (p1 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_6
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p4 p2 p5 p3 p7 p0 : Prop)
theorem file35_79501 : ((((((p3 → False) ∧ (p3 ∧ False)) → False) ∨ (((p7 ∨ p5) → (p0 → p4)) → ((p2 → p7) → (p0 → False)))) → False) → False) := by
  intro assump_10
  have assump_28 : ((((p3 → False) ∧ (p3 ∧ False)) → False) ∨ (((p7 ∨ p5) → (p0 → p4)) → ((p2 → p7) → (p0 → False)))) := by
    apply Or.inl
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        apply False.elim assump_20
  let assump_13 := assump_10 assump_28
  apply False.elim assump_13


variable (p1 p4 p2 p5 p6 p0 : Prop)
theorem file35_80088 : (((((True ∨ p5) → False) → False) ∨ (((False → False) ∧ (p4 ∧ p6)) ∧ ((p1 → False) → False))) ∨ ((((True → False) → False) → False) → (((p2 ∨ p0) → False) ∨ ((p5 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (True ∨ p5) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p4 p6 p1 : Prop)
theorem file35_80516 : ((((((False ∧ p4) → False) ∨ ((p3 ∨ p4) → False)) ∨ (((p4 → p1) ∧ (p6 ∨ False)) → ((p6 ∧ p4) ∨ (p3 → p4)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p4) → False) ∨ ((p3 ∨ p4) → False)) ∨ (((p4 → p1) ∧ (p6 ∨ False)) → ((p6 ∧ p4) ∨ (p3 → p4)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p7 p6 p3 p2 p4 p1 : Prop)
theorem file35_81064 : (((((p7 ∧ p4) ∨ (False → p7)) ∨ ((p2 ∨ p1) ∨ (p1 ∨ p4))) ∨ (((p7 ∨ False) ∧ (False ∨ False)) ∨ ((p3 → False) → (p4 → p6)))) ∧ ((((True ∧ p4) ∨ (p4 → True)) → False) → (((p5 → False) → (p5 ∨ p4)) → False))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply False.elim assump_1
  intro assump_4
  intro assump_5
  have assump_15 : ((True ∧ p4) ∨ (p4 → True)) := by
    apply Or.inr
    intro assump_11
    apply True.intro
  let assump_10 := assump_4 assump_15
  apply False.elim assump_10


variable (p1 p0 p4 p3 p6 p5 : Prop)
theorem file35_81656 : (((((True → False) ∧ (p0 ∧ p3)) → False) → False) → ((((p1 → False) → (p3 ∨ p0)) → ((True ∧ p5) ∨ (p4 ∧ True))) → (((False ∧ p6) ∨ (p1 → p3)) → ((p4 → False) → (True → p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_3
  case inl assump_10 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  case inr assump_11 =>
    have assump_43 : (((True → False) ∧ (p0 ∧ p3)) → False) := by
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          have assump_44 : True := by
            apply True.intro
          let assump_36 := assump_24 assump_44
          apply False.elim assump_36
    let assump_22 := assump_1 assump_43
    apply False.elim assump_22


variable (p5 p7 p2 p6 p0 p4 : Prop)
theorem file35_82577 : (((((p5 ∧ False) → False) ∨ ((p4 ∨ p0) → False)) → False) → ((((p7 ∨ p2) ∧ (p0 ∨ p2)) ∧ ((p5 → False) → False)) ∧ (((p6 → True) ∨ (True → p0)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  have assump_47 : (((p5 ∧ False) → False) ∨ ((p4 ∨ p0) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4
  have assump_48 : (((p5 ∧ False) → False) ∨ ((p4 ∨ p0) → False)) := by
    apply Or.inl
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      apply False.elim assump_20
  let assump_17 := assump_1 assump_48
  apply False.elim assump_17
  intro assump_28
  have assump_49 : (((p5 ∧ False) → False) ∨ ((p4 ∨ p0) → False)) := by
    apply Or.inl
    intro assump_34
    cases assump_34
    case intro assump_35 assump_36 =>
      apply False.elim assump_36
  let assump_33 := assump_1 assump_49
  apply False.elim assump_33
  apply Or.inl
  apply Or.inl
  intro assump_46
  apply True.intro


variable (p0 p4 p3 : Prop)
theorem file35_83755 : (((((p0 ∧ p4) ∧ (False ∧ p3)) → False) → False) → ((((p0 → False) → False) ∧ ((p3 → False) ∨ (p3 ∨ False))) ∨ (((p4 ∨ p4) ∨ (p4 → False)) ∨ ((True ∧ False) ∨ (p4 → p3))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_46 : (((p0 ∧ p4) ∧ (False ∧ p3)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
  let assump_8 := assump_1 assump_46
  apply False.elim assump_8
  apply Or.inl
  intro assump_25
  have assump_47 : (((p0 ∧ p4) ∧ (False ∧ p3)) → False) := by
    intro assump_30
    cases assump_30
    case intro assump_31 assump_32 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        cases assump_32
        case intro assump_39 assump_40 =>
          apply False.elim assump_39
  let assump_29 := assump_1 assump_47
  apply False.elim assump_29


variable (p7 p3 p1 p0 p6 p2 : Prop)
theorem file35_84833 : (((((p2 ∨ True) ∨ (p7 → False)) → False) → False) → ((((p2 ∧ p7) → False) → False) → (((p1 ∧ p6) ∧ (p0 ∧ p3)) ∨ ((p2 ∨ p1) ∨ (True ∨ p7))))) := by
  intro assump_1
  intro assump_2
  apply Or.inr
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p3 p2 p1 p6 p0 p7 p5 : Prop)
theorem file35_85141 : ((((((p3 ∨ p1) → (p3 ∨ p2)) ∧ ((p1 ∨ p3) → False)) ∧ (((p1 ∧ True) → (p6 → False)) ∧ ((p5 → False) ∨ (p2 → p1)))) ∧ ((((p0 → p2) ∧ (True ∨ p5)) → ((p7 → False) → False)) ∧ (((p1 ∧ p5) ∨ (p7 → p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              have assump_48 : ((p1 ∧ p5) ∨ (p7 → p7)) := by
                apply Or.inr
                intro assump_27
                exact assump_27
              let assump_26 := assump_21 assump_48
              apply False.elim assump_26
          case inr assump_17 =>
            cases assump_3
            case intro assump_35 assump_36 =>
              have assump_49 : ((p1 ∧ p5) ∨ (p7 → p7)) := by
                apply Or.inr
                intro assump_42
                exact assump_42
              let assump_41 := assump_36 assump_49
              apply False.elim assump_41


variable (p5 p1 p3 p7 p2 p4 p6 p0 : Prop)
theorem file35_86405 : (((((p4 → p2) ∨ (p1 ∧ p6)) ∧ ((p1 → p4) → (p3 ∨ p1))) ∧ (((p5 → p3) ∨ (p4 ∨ p2)) → False)) → ((((p1 ∨ True) → (p7 ∧ p1)) → ((p1 ∨ p6) ∨ (p0 ∧ p1))) → (((p4 ∧ p7) ∧ (p4 ∧ p0)) ∨ ((p7 ∧ False) → False)))) := by
  intro assump_29
  intro assump_30
  cases assump_29
  case intro assump_33 assump_34 =>
    cases assump_33
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        apply Or.inr
        intro assump_45
        cases assump_45
        case intro assump_46 assump_47 =>
          apply False.elim assump_47
      case inr assump_38 =>
        cases assump_38
        case intro assump_52 assump_53 =>
          apply Or.inr
          intro assump_62
          cases assump_62
          case intro assump_63 assump_64 =>
            apply False.elim assump_64


variable (p4 p2 p0 : Prop)
theorem file35_87263 : ((((((p0 → False) ∨ (p2 → False)) ∧ ((False → False) → (p4 → False))) → (((p2 → False) → (p0 ∨ True)) ∨ ((p4 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p0 → False) ∨ (p2 → False)) ∧ ((False → False) → (p4 → False))) → (((p2 → False) → (p0 ∨ True)) ∨ ((p4 → False) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_14
        apply Or.inr
        apply True.intro
      case inr assump_9 =>
        apply Or.inl
        intro assump_21
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p3 p2 p5 p4 : Prop)
theorem file35_88035 : (((((p4 → False) → (p5 → False)) → ((p3 → False) → (False → p2))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p4 → False) → (p5 → False)) → ((p3 → False) → (False → p2))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p4 p3 p6 p5 p7 p0 : Prop)
theorem file35_88443 : (((((p0 → p6) ∨ (p0 → False)) → ((p5 ∧ False) → (p6 → False))) ∨ (((p7 → False) → (p7 ∧ False)) ∧ ((p7 ∧ p0) ∨ (p7 ∧ p3)))) ∨ ((((False ∨ p6) → False) → False) ∧ (((p5 → False) ∨ (p7 ∧ p4)) → ((False ∧ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p3 p6 p0 p1 p7 p5 : Prop)
theorem file35_88891 : (((((p6 → False) ∨ (False ∨ p6)) → ((True → False) → False)) ∨ (((p0 ∨ True) ∨ (p6 ∨ p0)) → ((p0 → False) → (p3 → False)))) ∨ ((((p7 → True) → False) ∧ ((p1 → False) → (p5 ∨ p6))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    have assump_25 : True := by
      apply True.intro
    let assump_10 := assump_2 assump_25
    apply False.elim assump_10
  case inr assump_6 =>
    cases assump_6
    case inl assump_14 =>
      apply False.elim assump_14
    case inr assump_15 =>
      have assump_26 : True := by
        apply True.intro
      let assump_21 := assump_2 assump_26
      apply False.elim assump_21


variable (p4 p2 p0 p3 p7 : Prop)
theorem file35_89635 : (((((p2 ∧ p4) → (p4 ∨ p7)) ∨ ((p0 → False) → (p3 → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p2 ∧ p4) → (p4 ∨ p7)) ∨ ((p0 → False) → (p3 → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p3 p5 p7 : Prop)
theorem file35_90069 : (((((p3 ∨ p7) ∨ (p3 → False)) ∨ ((p0 ∧ p5) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p3 ∨ p7) ∨ (p3 → False)) ∨ ((p0 ∧ p5) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : (((p3 ∨ p7) ∨ (p3 → False)) ∨ ((p0 ∧ p5) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p0 p6 p5 : Prop)
theorem file35_90636 : ((((((p5 ∧ p4) → (p5 ∨ p0)) → False) ∧ (((p0 ∧ True) → False) ∧ ((True ∨ p5) ∨ (False ∧ p0)))) ∧ ((((p0 ∨ p6) → False) → ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            have assump_58 : (((p0 ∨ p6) → False) → ((True → False) → False)) := by
              intro assump_21
              intro assump_22
              have assump_59 : True := by
                apply True.intro
              let assump_28 := assump_22 assump_59
              apply False.elim assump_28
            let assump_20 := assump_3 assump_58
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_60 : (((p0 ∨ p6) → False) → ((True → False) → False)) := by
              intro assump_40
              intro assump_41
              have assump_61 : True := by
                apply True.intro
              let assump_47 := assump_41 assump_61
              apply False.elim assump_47
            let assump_39 := assump_3 assump_60
            apply False.elim assump_39
        case inr assump_13 =>
          cases assump_13
          case intro assump_54 assump_55 =>
            apply False.elim assump_54


variable (p1 p2 p6 p5 p7 : Prop)
theorem file35_92125 : (((((p6 ∧ p1) ∨ (p5 → p7)) ∨ ((True ∧ p2) → False)) → (((p7 → p1) ∧ (True → False)) → False)) ∨ ((((False → False) → False) ∧ ((True ∧ p2) ∨ (p5 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_39 : True := by
            apply True.intro
          let assump_21 := assump_4 assump_39
          apply False.elim assump_21
      case inr assump_12 =>
        have assump_40 : True := by
          apply True.intro
        let assump_28 := assump_4 assump_40
        apply False.elim assump_28
    case inr assump_10 =>
      have assump_41 : True := by
        apply True.intro
      let assump_35 := assump_4 assump_41
      apply False.elim assump_35


variable (p2 p4 p0 p7 : Prop)
theorem file35_93087 : (((((p4 → p4) ∧ (False ∧ p0)) ∧ ((True → False) ∨ (p7 ∧ p2))) ∧ (((p7 ∧ False) ∨ (p2 ∨ True)) ∨ ((p4 ∧ p2) → (False ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p5 p7 p3 p2 p4 p0 p6 p1 : Prop)
theorem file35_93577 : (((((p5 ∨ p6) ∧ (p7 ∨ p0)) → ((p3 ∧ False) → (False → p2))) ∧ (((p2 → p0) ∨ (p3 ∧ p4)) ∨ ((p0 ∨ p1) → (p1 ∨ p3)))) → ((((True ∧ p2) → (p4 ∨ p3)) → ((p0 ∧ p3) → (p2 ∨ True))) ∨ (((False → False) → (p6 ∨ p4)) → ((p0 → False) ∧ (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply Or.inr
          apply True.intro
      case inr assump_9 =>
        cases assump_9
        case intro assump_22 assump_23 =>
          apply Or.inl
          intro assump_28
          intro assump_29
          cases assump_29
          case intro assump_30 assump_31 =>
            apply Or.inr
            apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_40
      intro assump_41
      cases assump_41
      case intro assump_42 assump_43 =>
        apply Or.inr
        apply True.intro


variable (p3 p7 p6 p2 p0 p5 p1 : Prop)
theorem file35_94720 : (((((False ∧ p0) → (p6 ∨ p0)) → False) → False) ∨ ((((p5 ∧ p0) ∨ (False ∧ p1)) ∧ ((p3 → False) ∧ (p6 → False))) → (((p2 → p7) → False) ∨ ((True → False) ∧ (p1 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ p0) → (p6 ∨ p0)) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p4 p6 : Prop)
theorem file35_95198 : (((((p6 ∨ True) → False) → ((p4 ∧ p6) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : (((p6 ∨ True) → False) → ((p4 ∧ p6) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_23 : (p6 ∨ True) := by
        apply Or.inl
        exact assump_8
      let assump_15 := assump_5 assump_23
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p5 p2 p3 p4 : Prop)
theorem file35_95733 : ((((((True → True) ∨ (p7 ∧ p3)) ∨ ((p2 → False) → (False → False))) ∨ (((p2 → False) ∨ (True → p4)) → ((p7 → p5) → False))) → False) → False) := by
  intro assump_64
  have assump_72 : ((((True → True) ∨ (p7 ∧ p3)) ∨ ((p2 → False) → (False → False))) ∨ (((p2 → False) ∨ (True → p4)) → ((p7 → p5) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_68
    apply True.intro
  let assump_67 := assump_64 assump_72
  apply False.elim assump_67


variable (p3 p6 p7 p4 : Prop)
theorem file35_96260 : (((((p4 → p7) → False) → ((False → False) ∧ (p7 → p4))) → False) → ((((p6 → False) → False) → ((False → False) ∧ (p3 → False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_27 : (((p4 → p7) → False) → ((False → False) ∧ (p7 → p4))) := by
    intro assump_8
    apply And.intro
    intro assump_9
    apply False.elim assump_9
    intro assump_12
    have assump_28 : (p4 → p7) := by
      intro assump_18
      exact assump_12
    let assump_17 := assump_8 assump_28
    apply False.elim assump_17
  let assump_7 := assump_1 assump_27
  apply False.elim assump_7


variable (p1 p0 p2 p6 p3 p7 p5 : Prop)
theorem file35_96905 : ((((((p6 ∧ p0) → False) ∧ ((p6 → False) ∧ (p3 ∧ False))) → (((p7 ∧ False) → (p0 → False)) → ((p2 → p1) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p6 ∧ p0) → False) ∧ ((p6 → False) ∧ (p3 ∧ False))) → (((p7 ∧ False) → (p0 → False)) → ((p2 → p1) → (p5 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_5
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          apply False.elim assump_24
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 p6 p4 p0 p2 p5 : Prop)
theorem file35_97634 : (((((False ∨ p1) ∧ (p4 → False)) → ((p4 ∨ p1) → (False → False))) → False) → ((((True ∧ p5) ∧ (p0 ∧ p1)) ∧ ((p0 → False) → (p4 ∧ p2))) ∨ (((p4 ∨ p6) ∨ (p5 → False)) ∨ ((p0 → False) → (p1 → False))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  apply Or.inr
  intro assump_4
  have assump_17 : (((False ∨ p1) ∧ (p4 → False)) → ((p4 ∨ p1) → (False → False))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    apply False.elim assump_11
  let assump_8 := assump_1 assump_17
  apply False.elim assump_8


variable (p5 p4 p0 p3 p1 p2 p7 : Prop)
theorem file35_98226 : ((((((p3 ∧ False) ∨ (p1 → p5)) ∨ ((p5 → False) → (False ∨ p3))) → False) ∧ ((((p2 → False) → (p4 ∨ True)) → False) ∧ (((p1 ∧ False) → False) → ((p0 ∨ True) → (p7 → p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_29 : ((p2 → False) → (p4 ∨ True)) := by
        intro assump_23
        apply Or.inr
        apply True.intro
      let assump_22 := assump_6 assump_29
      apply False.elim assump_22


variable (p4 p3 p1 p5 p6 p2 : Prop)
theorem file35_98799 : (((((p3 ∨ True) ∨ (p6 ∨ False)) ∨ ((p1 ∨ p5) → False)) ∨ (((p4 → True) → False) ∧ ((p3 → p6) → (False ∧ False)))) ∨ ((((p3 → p2) ∧ (p2 ∨ True)) ∧ ((p1 ∨ p2) ∨ (p2 ∧ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p5 p6 p2 p7 p4 p0 p1 : Prop)
theorem file35_99143 : (((((p2 → False) ∧ (p4 ∨ p5)) → ((p1 → True) → (True → p4))) ∧ (((p4 ∧ p2) ∧ (p7 ∧ False)) ∧ ((p0 ∧ True) → (p4 ∨ p2)))) → ((((p2 ∧ p2) ∧ (p5 → False)) ∨ ((True → False) ∨ (p7 ∧ p4))) ∧ (((p5 ∧ p5) ∨ (p1 → False)) → ((p5 ∧ p6) ∨ (p7 ∧ p4))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
  intro assump_22
  cases assump_22
  case inl assump_23 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_1
      case intro assump_31 assump_32 =>
        cases assump_32
        case intro assump_35 assump_36 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            cases assump_37
            case intro assump_39 assump_40 =>
              cases assump_38
              case intro assump_45 assump_46 =>
                apply False.elim assump_46
  case inr assump_24 =>
    cases assump_1
    case intro assump_53 assump_54 =>
      cases assump_54
      case intro assump_57 assump_58 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          cases assump_59
          case intro assump_61 assump_62 =>
            cases assump_60
            case intro assump_67 assump_68 =>
              apply False.elim assump_68


variable (p7 p2 p6 p3 p4 p5 : Prop)
theorem file35_100729 : (((((p2 ∧ False) → (True ∧ p2)) → False) ∧ (((p4 ∨ p3) ∨ (p3 → p7)) ∧ ((p4 ∧ True) → False))) → ((((p6 → False) → (p5 ∨ False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          have assump_57 : (p4 ∧ True) := by
            apply And.intro
            exact assump_13
            apply True.intro
          let assump_19 := assump_10 assump_57
          apply False.elim assump_19
        case inr assump_14 =>
          have assump_58 : ((p2 ∧ False) → (True ∧ p2)) := by
            intro assump_30
            apply And.intro
            apply True.intro
            cases assump_30
            case intro assump_31 assump_32 =>
              apply False.elim assump_32
          let assump_29 := assump_5 assump_58
          apply False.elim assump_29
      case inr assump_12 =>
        have assump_59 : ((p2 ∧ False) → (True ∧ p2)) := by
          intro assump_47
          apply And.intro
          apply True.intro
          cases assump_47
          case intro assump_48 assump_49 =>
            apply False.elim assump_49
        let assump_46 := assump_5 assump_59
        apply False.elim assump_46


variable (p2 p3 p0 p5 : Prop)
theorem file35_102124 : ((((((p2 ∧ False) → (True ∨ p5)) ∨ ((True → True) → (False ∧ p5))) ∨ (((p3 → p0) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∧ False) → (True ∨ p5)) ∨ ((True → True) → (False ∧ p5))) ∨ (((p3 → p0) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p3 p7 p1 p4 p6 p0 : Prop)
theorem file35_102656 : ((((((p7 → p0) ∧ (True → False)) → ((p3 ∨ True) → False)) → (((p5 ∧ False) → (p4 → p1)) ∨ ((p7 → False) ∧ (p6 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p7 → p0) ∧ (True → False)) → ((p3 ∨ True) → False)) → (((p5 ∧ False) → (p4 → p1)) ∨ ((p7 → False) ∧ (p6 ∧ False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 p7 p4 p6 p2 p0 p1 p5 : Prop)
theorem file35_103259 : ((((((p0 → False) ∨ (p6 ∧ p7)) ∨ ((p7 → p4) → (True ∧ p4))) → (((p1 ∧ p5) ∨ (p4 ∨ p4)) → ((False ∨ p5) ∨ (False ∧ p5)))) ∧ ((((p3 ∨ p2) ∧ (p2 → False)) ∨ ((False → True) ∨ (True → p4))) → False)) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    have assump_18 : (((p3 ∨ p2) ∧ (p2 → False)) ∨ ((False → True) ∨ (True → p4))) := by
      apply Or.inr
      apply Or.inl
      intro assump_14
      apply True.intro
    let assump_13 := assump_8 assump_18
    apply False.elim assump_13


variable (p7 p3 p6 p1 p2 : Prop)
theorem file35_103838 : (((((p7 → False) ∨ (p2 → True)) ∨ ((True ∧ p7) → (True ∧ p2))) ∧ (((False → False) → False) ∧ ((p6 → p1) ∨ (False ∨ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            have assump_104 : (False → False) := by
              intro assump_20
              apply False.elim assump_20
            let assump_19 := assump_10 assump_104
            apply False.elim assump_19
          case inr assump_15 =>
            cases assump_15
            case inl assump_26 =>
              apply False.elim assump_26
            case inr assump_27 =>
              have assump_105 : (False → False) := by
                intro assump_34
                apply False.elim assump_34
              let assump_33 := assump_10 assump_105
              apply False.elim assump_33
      case inr assump_7 =>
        cases assump_3
        case intro assump_42 assump_43 =>
          cases assump_43
          case inl assump_46 =>
            have assump_106 : (False → False) := by
              intro assump_52
              apply False.elim assump_52
            let assump_51 := assump_42 assump_106
            apply False.elim assump_51
          case inr assump_47 =>
            cases assump_47
            case inl assump_58 =>
              apply False.elim assump_58
            case inr assump_59 =>
              have assump_107 : (False → False) := by
                intro assump_66
                apply False.elim assump_66
              let assump_65 := assump_42 assump_107
              apply False.elim assump_65
    case inr assump_5 =>
      cases assump_3
      case intro assump_74 assump_75 =>
        cases assump_75
        case inl assump_78 =>
          have assump_108 : (False → False) := by
            intro assump_84
            apply False.elim assump_84
          let assump_83 := assump_74 assump_108
          apply False.elim assump_83
        case inr assump_79 =>
          cases assump_79
          case inl assump_90 =>
            apply False.elim assump_90
          case inr assump_91 =>
            have assump_109 : (False → False) := by
              intro assump_98
              apply False.elim assump_98
            let assump_97 := assump_74 assump_109
            apply False.elim assump_97


variable (p2 p7 p6 p0 : Prop)
theorem file35_106382 : (((((p6 ∨ p7) → (p6 → True)) ∨ ((False ∧ p0) → (p2 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_10 : (((p6 ∨ p7) → (p6 → True)) ∨ ((False ∧ p0) → (p2 ∧ p6))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p5 p1 p2 p0 p3 p6 : Prop)
theorem file35_106765 : ((((((p0 → False) → (True ∨ True)) ∨ ((p3 ∨ p5) → False)) ∨ (((p1 ∨ False) → (p3 → False)) ∧ ((p2 → p6) → False))) → False) → False) := by
  intro assump_10
  have assump_20 : ((((p0 → False) → (True ∨ True)) ∨ ((p3 ∨ p5) → False)) ∨ (((p1 ∨ False) → (p3 → False)) ∧ ((p2 → p6) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_14
    apply Or.inl
    apply True.intro
  let assump_13 := assump_10 assump_20
  apply False.elim assump_13


variable (p6 p1 p3 p5 p7 p2 p4 : Prop)
theorem file35_107283 : (((((True → False) ∧ (p6 → False)) → ((p3 ∨ p5) → (p2 → p2))) ∧ (((p5 → False) → False) ∧ ((p4 ∨ True) → False))) → ((((p2 ∨ p6) ∧ (True → p1)) → False) → (((True → p7) → False) → ((False ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p6 p4 p5 p7 p2 p3 : Prop)
theorem file35_107704 : ((((((p2 → p6) → False) ∧ ((p2 → False) ∧ (p3 → p2))) → (((p7 → p6) → (p4 → p4)) → ((p2 ∨ True) ∨ (False → p5)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p2 → p6) → False) ∧ ((p2 → False) ∧ (p3 → p2))) → (((p7 → p6) → (p4 → p4)) → ((p2 ∨ True) ∨ (False → p5)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p1 p4 p6 p3 p7 p5 : Prop)
theorem file35_108347 : ((((((p4 ∨ p7) → False) → ((p2 ∨ p4) → (p2 ∨ p2))) → False) ∨ ((((p2 ∨ True) ∧ (p7 → True)) → False) ∧ (((p3 ∧ p3) ∧ (True ∨ p5)) ∨ ((p2 ∧ p1) → (p6 ∨ True))))) → False) := by
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    have assump_75 : (((p4 ∨ p7) → False) → ((p2 ∨ p4) → (p2 ∨ p2))) := by
      intro assump_13
      intro assump_14
      cases assump_14
      case inl assump_15 =>
        apply Or.inl
        exact assump_15
      case inr assump_16 =>
        have assump_76 : (p4 ∨ p7) := by
          apply Or.inl
          exact assump_16
        let assump_25 := assump_13 assump_76
        apply False.elim assump_25
    let assump_12 := assump_8 assump_75
    apply False.elim assump_12
  case inr assump_9 =>
    cases assump_9
    case intro assump_32 assump_33 =>
      cases assump_33
      case inl assump_36 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            cases assump_39
            case inl assump_46 =>
              have assump_77 : ((p2 ∨ True) ∧ (p7 → True)) := by
                apply And.intro
                apply Or.inr
                apply True.intro
                intro assump_53
                apply True.intro
              let assump_52 := assump_32 assump_77
              apply False.elim assump_52
            case inr assump_47 =>
              have assump_78 : ((p2 ∨ True) ∧ (p7 → True)) := by
                apply And.intro
                apply Or.inr
                apply True.intro
                intro assump_63
                apply True.intro
              let assump_62 := assump_32 assump_78
              apply False.elim assump_62
      case inr assump_37 =>
        have assump_79 : ((p2 ∨ True) ∧ (p7 → True)) := by
          apply And.intro
          apply Or.inr
          apply True.intro
          intro assump_71
          apply True.intro
        let assump_70 := assump_32 assump_79
        apply False.elim assump_70


variable (p5 p6 p1 p3 p0 : Prop)
theorem file35_110410 : (((((True ∧ p6) → (p6 → False)) → ((p3 ∨ p1) ∧ (p5 → p1))) ∧ (((p0 → False) → (p0 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : ((p0 → False) → (p0 → False)) := by
      intro assump_9
      intro assump_10
      have assump_23 : p0 := by
        exact assump_10
      let assump_15 := assump_9 assump_23
      apply False.elim assump_15
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p6 p2 p4 p7 p5 p3 p0 : Prop)
theorem file35_110958 : (((((False ∨ p0) ∨ (False ∧ p4)) ∧ ((p6 → p4) ∨ (False ∨ p4))) ∨ (((p2 → p7) ∧ (p3 → False)) → False)) → ((((p0 → False) → False) ∧ ((False ∨ p5) → (True → p7))) → (((p2 → True) ∨ (p6 ∧ p0)) ∨ ((False ∧ p0) ∨ (p4 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            apply False.elim assump_15
          case inr assump_16 =>
            cases assump_12
            case inl assump_21 =>
              apply Or.inl
              apply Or.inl
              intro assump_25
              apply True.intro
            case inr assump_22 =>
              cases assump_22
              case inl assump_26 =>
                apply False.elim assump_26
              case inr assump_27 =>
                apply Or.inl
                apply Or.inl
                intro assump_32
                apply True.intro
        case inr assump_14 =>
          cases assump_14
          case intro assump_33 assump_34 =>
            apply False.elim assump_33
    case inr assump_10 =>
      apply Or.inl
      apply Or.inl
      intro assump_39
      apply True.intro


variable (p3 p4 p7 p5 p6 p2 : Prop)
theorem file35_112347 : ((((((p5 → False) ∧ (True → p4)) ∧ ((p6 ∧ p3) → (p7 → p4))) → (((p2 → True) → False) → ((p4 ∨ p4) → (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_62 : ((((p5 → False) ∧ (True → p4)) ∧ ((p6 ∧ p3) → (p7 → p4))) → (((p2 → True) → False) → ((p4 ∨ p4) → (p3 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          have assump_63 : (p2 → True) := by
            intro assump_32
            apply True.intro
          let assump_31 := assump_6 assump_63
          apply False.elim assump_31
    case inr assump_12 =>
      cases assump_5
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          have assump_64 : (p2 → True) := by
            intro assump_55
            apply True.intro
          let assump_54 := assump_6 assump_64
          apply False.elim assump_54
  let assump_4 := assump_1 assump_62
  apply False.elim assump_4


variable (p1 p0 p3 p4 : Prop)
theorem file35_113533 : (((((p4 ∧ False) ∨ (p1 → p1)) ∨ ((p0 ∨ p3) ∨ (p4 ∧ True))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p4 ∧ False) ∨ (p1 → p1)) ∨ ((p0 ∨ p3) ∨ (p4 ∧ True))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p7 p1 p3 p0 : Prop)
theorem file35_113909 : (((((p0 ∨ p1) ∨ (p1 → False)) → False) → False) ∨ ((((p7 → False) → False) ∧ ((True → p3) → (p7 ∧ p5))) ∨ (((p3 → p5) → False) ∨ ((p1 → True) ∨ (p7 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  have assump_16 : ((p0 ∨ p1) ∨ (p1 → False)) := by
    apply Or.inr
    intro assump_5
    have assump_17 : ((p0 ∨ p1) ∨ (p1 → False)) := by
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p3 p2 p7 : Prop)
theorem file35_114494 : (((((p7 → p2) → False) → ((True ∨ False) ∨ (False → False))) ∨ (((p5 → False) → False) → ((p3 → False) → False))) ∨ ((((False ∨ p5) → False) → ((p2 → p5) → (p7 ∨ p7))) → (((p2 ∨ p3) ∨ (True → False)) ∧ ((p3 ∧ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p4 p2 p3 p7 p0 p5 p6 p1 : Prop)
theorem file35_114889 : (((((p4 ∨ True) → False) ∧ ((p2 ∧ p2) → False)) → (((True → False) ∧ (False ∧ p6)) ∧ ((p2 ∨ p3) ∧ (True → True)))) ∨ ((((False ∧ False) → (True ∨ False)) ∧ ((p7 → p1) ∧ (p4 → False))) ∨ (((p0 → False) → (p7 ∨ p5)) → ((p2 → p5) ∨ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_50 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_5 assump_50
    apply False.elim assump_12
  apply And.intro
  cases assump_1
  case intro assump_16 assump_17 =>
    have assump_51 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_23 := assump_16 assump_51
    apply False.elim assump_23
  cases assump_1
  case intro assump_27 assump_28 =>
    have assump_52 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_34 := assump_27 assump_52
    apply False.elim assump_34
  apply And.intro
  cases assump_1
  case intro assump_38 assump_39 =>
    have assump_53 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_45 := assump_38 assump_53
    apply False.elim assump_45
  intro assump_49
  apply True.intro


variable (p1 p3 p0 p6 p2 p7 p4 : Prop)
theorem file35_116183 : (((((p2 → False) ∨ (p6 → p0)) → ((p7 ∧ True) → False)) ∧ (((p3 ∨ p1) ∨ (p4 → False)) ∧ ((p4 ∧ False) ∧ (True → p4)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
        case inr assump_15 =>
          cases assump_11
          case intro assump_28 assump_29 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              apply False.elim assump_31
      case inr assump_13 =>
        cases assump_11
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_41


variable (p0 p6 p5 p3 p7 p1 : Prop)
theorem file35_117208 : (((((p3 → p6) → (p0 ∧ p1)) → ((p5 → True) ∨ (False → p7))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p3 → p6) → (p0 ∧ p1)) → ((p5 → True) ∨ (False → p7))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p6 p0 p5 p1 p7 p3 : Prop)
theorem file35_117594 : (((((p0 → p3) ∧ (p1 ∨ p2)) ∨ ((p2 → p7) ∧ (True → False))) → False) → ((((False → p2) → False) → ((p6 ∨ p2) ∧ (p7 ∧ True))) ∨ (((p6 ∧ True) ∨ (False → False)) → ((p1 → p6) → (p5 ∨ p6))))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  apply And.intro
  have assump_27 : (False → p2) := by
    intro assump_12
    apply False.elim assump_12
  let assump_11 := assump_8 assump_27
  apply False.elim assump_11
  apply And.intro
  have assump_28 : (False → p2) := by
    intro assump_21
    apply False.elim assump_21
  let assump_20 := assump_8 assump_28
  apply False.elim assump_20
  apply True.intro


variable (p6 p0 p3 p5 p4 p7 p1 : Prop)
theorem file35_118267 : (((((p0 ∨ p0) ∨ (p6 ∨ True)) → ((p6 → False) ∨ (True → p3))) ∨ (((True → False) → (p0 → p5)) → ((p3 → False) ∨ (p1 → p6)))) → ((((False → True) ∧ (p5 ∧ p3)) → ((False ∨ p5) ∧ (False → p4))) ∨ (((p4 ∨ p4) → (p3 → p7)) ∧ ((True ∧ True) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply Or.inr
        exact assump_11
    intro assump_17
    apply False.elim assump_17
  case inr assump_3 =>
    apply Or.inl
    intro assump_22
    apply And.intro
    cases assump_22
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        apply Or.inr
        exact assump_27
    intro assump_33
    apply False.elim assump_33


variable (p7 p3 p6 p5 p0 p4 : Prop)
theorem file35_119200 : ((((((p4 → False) → False) ∨ ((p0 ∧ p7) ∧ (p4 → False))) → (((False → False) ∧ (p7 → True)) ∨ ((p3 ∧ p5) → (p6 → p0)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p4 → False) → False) ∨ ((p0 ∧ p7) ∧ (p4 → False))) → (((False → False) ∧ (p7 → True)) ∨ ((p3 ∧ p5) → (p6 → p0)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply And.intro
      intro assump_10
      apply False.elim assump_10
      intro assump_13
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply Or.inl
          apply And.intro
          intro assump_24
          apply False.elim assump_24
          intro assump_27
          apply True.intro
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p5 p6 p2 p0 p7 p1 : Prop)
theorem file35_120150 : (((((p1 ∨ p0) ∧ (True → True)) → ((p6 ∨ p1) ∨ (p7 ∨ p0))) ∨ (((p0 ∧ False) ∨ (False ∧ True)) ∨ ((p0 ∧ p0) ∨ (p2 ∨ True)))) ∨ ((((p0 ∧ p6) ∨ (p5 ∧ p7)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inr
      exact assump_4
    case inr assump_5 =>
      apply Or.inr
      apply Or.inr
      exact assump_5


variable (p1 p6 p7 p0 p5 : Prop)
theorem file35_120668 : (((((p6 ∧ p7) → (p6 ∨ p0)) ∨ ((True ∧ p5) ∨ (p1 ∨ p5))) → False) → False) := by
  intro assump_5
  have assump_19 : (((p6 ∧ p7) → (p6 ∨ p0)) ∨ ((True ∧ p5) ∨ (p1 ∨ p5))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply Or.inl
      exact assump_10
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p3 p2 p5 p1 p0 p4 p6 p7 : Prop)
theorem file35_121109 : (((((p7 ∨ p4) ∧ (False ∨ p5)) → False) → (((p2 → p7) → (p7 → True)) ∨ ((False ∧ p1) ∧ (p0 → False)))) ∨ ((((p1 ∧ p2) ∧ (p7 → False)) ∨ ((p0 ∨ p0) ∨ (p7 → False))) ∧ (((p0 ∨ p2) ∨ (p2 ∨ p1)) ∨ ((p3 ∨ p6) ∨ (p5 → True))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p7 p3 p6 p0 p1 p4 p2 : Prop)
theorem file35_121499 : (((((p2 ∧ p3) → (p6 ∧ p1)) ∧ ((p4 ∧ p6) ∧ (p6 ∧ p3))) → (((p2 ∧ p7) → False) ∧ ((p2 ∨ p1) ∨ (p4 → False)))) → ((((p7 → False) → False) ∨ ((p1 ∨ p2) ∨ (p0 → False))) → (((p3 → False) → (p0 → False)) → ((True → True) ∨ (p1 ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    apply Or.inl
    intro assump_12
    apply True.intro
  case inr assump_7 =>
    cases assump_7
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        apply Or.inl
        intro assump_21
        apply True.intro
      case inr assump_16 =>
        apply Or.inl
        intro assump_26
        apply True.intro
    case inr assump_14 =>
      apply Or.inl
      intro assump_31
      apply True.intro


variable (p6 p4 p0 p7 p3 p2 p5 : Prop)
theorem file35_122324 : ((((((p3 ∨ True) ∧ (p5 ∨ p0)) ∨ ((True → False) → (p5 → True))) ∨ (((p3 → p5) → False) ∧ ((p7 ∨ p6) → (p7 → False)))) ∧ ((((p0 ∧ p6) ∧ (p4 ∨ p5)) ∨ ((p7 ∨ True) → (p2 ∨ True))) → False)) → False) := by
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
          case inl assump_10 =>
            cases assump_9
            case inl assump_14 =>
              have assump_114 : (((p0 ∧ p6) ∧ (p4 ∨ p5)) ∨ ((p7 ∨ True) → (p2 ∨ True))) := by
                apply Or.inr
                intro assump_21
                cases assump_21
                case inl assump_22 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_23 =>
                  apply Or.inr
                  apply True.intro
              let assump_20 := assump_3 assump_114
              apply False.elim assump_20
            case inr assump_15 =>
              have assump_115 : (((p0 ∧ p6) ∧ (p4 ∨ p5)) ∨ ((p7 ∨ True) → (p2 ∨ True))) := by
                apply Or.inr
                intro assump_36
                cases assump_36
                case inl assump_37 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_38 =>
                  apply Or.inr
                  apply True.intro
              let assump_35 := assump_3 assump_115
              apply False.elim assump_35
          case inr assump_11 =>
            cases assump_9
            case inl assump_48 =>
              have assump_116 : (((p0 ∧ p6) ∧ (p4 ∨ p5)) ∨ ((p7 ∨ True) → (p2 ∨ True))) := by
                apply Or.inr
                intro assump_55
                cases assump_55
                case inl assump_56 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_57 =>
                  apply Or.inr
                  apply True.intro
              let assump_54 := assump_3 assump_116
              apply False.elim assump_54
            case inr assump_49 =>
              have assump_117 : (((p0 ∧ p6) ∧ (p4 ∨ p5)) ∨ ((p7 ∨ True) → (p2 ∨ True))) := by
                apply Or.inr
                intro assump_70
                cases assump_70
                case inl assump_71 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_72 =>
                  apply Or.inr
                  apply True.intro
              let assump_69 := assump_3 assump_117
              apply False.elim assump_69
      case inr assump_7 =>
        have assump_118 : (((p0 ∧ p6) ∧ (p4 ∨ p5)) ∨ ((p7 ∨ True) → (p2 ∨ True))) := by
          apply Or.inr
          intro assump_85
          cases assump_85
          case inl assump_86 =>
            apply Or.inr
            apply True.intro
          case inr assump_87 =>
            apply Or.inr
            apply True.intro
        let assump_84 := assump_3 assump_118
        apply False.elim assump_84
    case inr assump_5 =>
      cases assump_5
      case intro assump_95 assump_96 =>
        have assump_119 : (((p0 ∧ p6) ∧ (p4 ∨ p5)) ∨ ((p7 ∨ True) → (p2 ∨ True))) := by
          apply Or.inr
          intro assump_104
          cases assump_104
          case inl assump_105 =>
            apply Or.inr
            apply True.intro
          case inr assump_106 =>
            apply Or.inr
            apply True.intro
        let assump_103 := assump_3 assump_119
        apply False.elim assump_103


