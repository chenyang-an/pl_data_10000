variable (p6 p5 p0 p1 p2 p4 : Prop)
theorem file64_44 : ((((((p5 → False) ∧ (p4 → p6)) → ((p0 → False) → (p0 → p1))) → (((p2 ∨ p4) ∨ (p0 ∨ True)) ∨ ((p1 → p1) ∨ (True ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 → False) ∧ (p4 → p6)) → ((p0 → False) → (p0 → p1))) → (((p2 ∨ p4) ∨ (p0 ∨ True)) ∨ ((p1 → p1) ∨ (True ∨ p0)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p4 p5 p3 p1 : Prop)
theorem file64_561 : ((((((False ∧ False) → False) ∨ ((p5 ∧ p1) → False)) ∨ (((p3 ∧ p4) → False) ∧ ((p4 → False) ∨ (p6 ∨ p6)))) → False) → False) := by
  intro assump_24
  have assump_36 : ((((False ∧ False) → False) ∨ ((p5 ∧ p1) → False)) ∨ (((p3 ∧ p4) → False) ∧ ((p4 → False) ∨ (p6 ∨ p6)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      apply False.elim assump_29
  let assump_27 := assump_24 assump_36
  apply False.elim assump_27


variable (p3 p4 p7 p2 p1 p6 p5 p0 : Prop)
theorem file64_1119 : (((((p1 ∧ p6) ∧ (p7 ∨ False)) ∨ ((p7 ∨ p7) ∧ (p0 ∧ p3))) → (((False → True) ∨ (True → p2)) → ((p5 → False) → (False → p6)))) ∨ ((((p4 → p3) → (True ∧ False)) ∧ ((p7 ∧ p7) ∧ (p5 ∨ p6))) → (((True ∨ False) ∨ (False → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p4 p5 p7 p0 p2 p3 p6 p1 : Prop)
theorem file64_1536 : (((((p3 → True) → False) → ((p7 → False) → (p1 → False))) ∧ (((p7 ∨ p1) → False) → ((p1 ∧ p7) → (p3 → p3)))) ∨ ((((p0 → p0) → (p2 → False)) → False) ∨ (((p5 → p6) → (p1 ∧ p4)) → ((p6 → False) → False)))) := by
  apply Or.inl
  apply And.intro
  intro assump_27
  intro assump_28
  intro assump_29
  have assump_54 : (p3 → True) := by
    intro assump_37
    apply True.intro
  let assump_36 := assump_27 assump_54
  apply False.elim assump_36
  intro assump_41
  intro assump_42
  intro assump_43
  cases assump_42
  case intro assump_46 assump_47 =>
    exact assump_43


variable (p0 p6 p7 p1 p5 : Prop)
theorem file64_2164 : (((((p0 ∨ p5) ∨ (False → False)) → False) → False) ∨ ((((p1 ∨ p0) → False) ∨ ((True ∧ p5) ∨ (True ∧ p1))) → (((p6 ∨ False) ∧ (False ∧ p7)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p0 ∨ p5) ∨ (False → False)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p1 p7 p2 p5 p0 p3 p4 : Prop)
theorem file64_2604 : (((((False → False) → False) → ((p4 ∨ p1) → (p0 ∨ p6))) → (((p6 → False) ∨ (p3 → False)) → ((False ∧ p1) → False))) ∨ ((((p0 ∧ p7) → (True ∧ p3)) ∨ ((p2 → p7) → (True ∨ True))) ∧ (((p3 ∧ p6) → False) ∨ ((p5 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4


variable (p4 p1 p3 p6 p7 p2 p5 p0 : Prop)
theorem file64_3051 : ((((((p1 ∧ p6) ∧ (p2 ∨ p7)) ∧ ((p2 → False) ∧ (p3 → p4))) ∧ (((p3 ∨ p5) → False) → False)) ∧ ((((p0 ∨ p7) ∨ (p1 ∧ p1)) ∨ ((True ∧ p6) → (p6 ∧ p4))) ∧ (((p1 → p1) ∧ (p0 ∨ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_9
            case inl assump_16 =>
              cases assump_7
              case intro assump_20 assump_21 =>
                cases assump_3
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case inl assump_30 =>
                    cases assump_30
                    case inl assump_32 =>
                      cases assump_32
                      case inl assump_34 =>
                        have assump_150 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                          apply And.intro
                          intro assump_41
                          exact assump_41
                          apply Or.inl
                          exact assump_34
                        let assump_40 := assump_29 assump_150
                        apply False.elim assump_40
                      case inr assump_35 =>
                        have assump_151 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                          apply And.intro
                          intro assump_52
                          exact assump_52
                          apply Or.inr
                          exact assump_11
                        let assump_51 := assump_29 assump_151
                        apply False.elim assump_51
                    case inr assump_33 =>
                      cases assump_33
                      case intro assump_58 assump_59 =>
                        have assump_152 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                          apply And.intro
                          intro assump_67
                          exact assump_67
                          apply Or.inr
                          exact assump_11
                        let assump_66 := assump_29 assump_152
                        apply False.elim assump_66
                  case inr assump_31 =>
                    have assump_153 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                      apply And.intro
                      intro assump_78
                      exact assump_78
                      apply Or.inr
                      exact assump_11
                    let assump_77 := assump_29 assump_153
                    apply False.elim assump_77
            case inr assump_17 =>
              cases assump_7
              case intro assump_86 assump_87 =>
                cases assump_3
                case intro assump_94 assump_95 =>
                  cases assump_94
                  case inl assump_96 =>
                    cases assump_96
                    case inl assump_98 =>
                      cases assump_98
                      case inl assump_100 =>
                        have assump_154 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                          apply And.intro
                          intro assump_107
                          exact assump_107
                          apply Or.inl
                          exact assump_100
                        let assump_106 := assump_95 assump_154
                        apply False.elim assump_106
                      case inr assump_101 =>
                        have assump_155 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                          apply And.intro
                          intro assump_118
                          exact assump_118
                          apply Or.inr
                          exact assump_11
                        let assump_117 := assump_95 assump_155
                        apply False.elim assump_117
                    case inr assump_99 =>
                      cases assump_99
                      case intro assump_124 assump_125 =>
                        have assump_156 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                          apply And.intro
                          intro assump_133
                          exact assump_133
                          apply Or.inr
                          exact assump_11
                        let assump_132 := assump_95 assump_156
                        apply False.elim assump_132
                  case inr assump_97 =>
                    have assump_157 : ((p1 → p1) ∧ (p0 ∨ p6)) := by
                      apply And.intro
                      intro assump_144
                      exact assump_144
                      apply Or.inr
                      exact assump_11
                    let assump_143 := assump_95 assump_157
                    apply False.elim assump_143


variable (p6 p3 p7 p0 p5 p4 p2 p1 : Prop)
theorem file64_8044 : (((((p5 ∨ p5) ∨ (p1 → p2)) ∧ ((False → p2) ∨ (p3 ∨ p6))) ∧ (((True ∨ p2) → False) ∨ ((p7 → False) → (True → False)))) → ((((p2 → False) → (p5 → False)) ∨ ((p1 ∧ p0) → False)) → (((p7 → False) → (p7 ∨ p2)) ∨ ((p6 → p0) ∧ (p4 → p0))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_11
          case inl assump_13 =>
            cases assump_10
            case inl assump_17 =>
              cases assump_8
              case inl assump_21 =>
                apply Or.inl
                intro assump_25
                have assump_655 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_29 := assump_21 assump_655
                apply False.elim assump_29
              case inr assump_22 =>
                apply Or.inl
                intro assump_35
                have assump_656 : (p7 → False) := by
                  intro assump_40
                  have assump_657 : p7 := by
                    exact assump_40
                  let assump_44 := assump_35 assump_657
                  apply False.elim assump_44
                let assump_39 := assump_22 assump_656
                have assump_658 : True := by
                  apply True.intro
                let assump_48 := assump_39 assump_658
                apply False.elim assump_48
            case inr assump_18 =>
              cases assump_18
              case inl assump_52 =>
                cases assump_8
                case inl assump_56 =>
                  apply Or.inl
                  intro assump_60
                  have assump_659 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_64 := assump_56 assump_659
                  apply False.elim assump_64
                case inr assump_57 =>
                  apply Or.inl
                  intro assump_70
                  have assump_660 : (p7 → False) := by
                    intro assump_75
                    have assump_661 : p7 := by
                      exact assump_75
                    let assump_79 := assump_70 assump_661
                    apply False.elim assump_79
                  let assump_74 := assump_57 assump_660
                  have assump_662 : True := by
                    apply True.intro
                  let assump_83 := assump_74 assump_662
                  apply False.elim assump_83
              case inr assump_53 =>
                cases assump_8
                case inl assump_89 =>
                  apply Or.inl
                  intro assump_93
                  have assump_663 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_97 := assump_89 assump_663
                  apply False.elim assump_97
                case inr assump_90 =>
                  apply Or.inl
                  intro assump_103
                  have assump_664 : (p7 → False) := by
                    intro assump_108
                    have assump_665 : p7 := by
                      exact assump_108
                    let assump_112 := assump_103 assump_665
                    apply False.elim assump_112
                  let assump_107 := assump_90 assump_664
                  have assump_666 : True := by
                    apply True.intro
                  let assump_116 := assump_107 assump_666
                  apply False.elim assump_116
          case inr assump_14 =>
            cases assump_10
            case inl assump_122 =>
              cases assump_8
              case inl assump_126 =>
                apply Or.inl
                intro assump_130
                have assump_667 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_134 := assump_126 assump_667
                apply False.elim assump_134
              case inr assump_127 =>
                apply Or.inl
                intro assump_140
                have assump_668 : (p7 → False) := by
                  intro assump_145
                  have assump_669 : p7 := by
                    exact assump_145
                  let assump_149 := assump_140 assump_669
                  apply False.elim assump_149
                let assump_144 := assump_127 assump_668
                have assump_670 : True := by
                  apply True.intro
                let assump_153 := assump_144 assump_670
                apply False.elim assump_153
            case inr assump_123 =>
              cases assump_123
              case inl assump_157 =>
                cases assump_8
                case inl assump_161 =>
                  apply Or.inl
                  intro assump_165
                  have assump_671 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_169 := assump_161 assump_671
                  apply False.elim assump_169
                case inr assump_162 =>
                  apply Or.inl
                  intro assump_175
                  have assump_672 : (p7 → False) := by
                    intro assump_180
                    have assump_673 : p7 := by
                      exact assump_180
                    let assump_184 := assump_175 assump_673
                    apply False.elim assump_184
                  let assump_179 := assump_162 assump_672
                  have assump_674 : True := by
                    apply True.intro
                  let assump_188 := assump_179 assump_674
                  apply False.elim assump_188
              case inr assump_158 =>
                cases assump_8
                case inl assump_194 =>
                  apply Or.inl
                  intro assump_198
                  have assump_675 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_202 := assump_194 assump_675
                  apply False.elim assump_202
                case inr assump_195 =>
                  apply Or.inl
                  intro assump_208
                  have assump_676 : (p7 → False) := by
                    intro assump_213
                    have assump_677 : p7 := by
                      exact assump_213
                    let assump_217 := assump_208 assump_677
                    apply False.elim assump_217
                  let assump_212 := assump_195 assump_676
                  have assump_678 : True := by
                    apply True.intro
                  let assump_221 := assump_212 assump_678
                  apply False.elim assump_221
        case inr assump_12 =>
          cases assump_10
          case inl assump_227 =>
            cases assump_8
            case inl assump_231 =>
              apply Or.inl
              intro assump_235
              have assump_679 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_239 := assump_231 assump_679
              apply False.elim assump_239
            case inr assump_232 =>
              apply Or.inl
              intro assump_245
              have assump_680 : (p7 → False) := by
                intro assump_250
                have assump_681 : p7 := by
                  exact assump_250
                let assump_254 := assump_245 assump_681
                apply False.elim assump_254
              let assump_249 := assump_232 assump_680
              have assump_682 : True := by
                apply True.intro
              let assump_258 := assump_249 assump_682
              apply False.elim assump_258
          case inr assump_228 =>
            cases assump_228
            case inl assump_262 =>
              cases assump_8
              case inl assump_266 =>
                apply Or.inl
                intro assump_270
                have assump_683 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_274 := assump_266 assump_683
                apply False.elim assump_274
              case inr assump_267 =>
                apply Or.inl
                intro assump_280
                have assump_684 : (p7 → False) := by
                  intro assump_285
                  have assump_685 : p7 := by
                    exact assump_285
                  let assump_289 := assump_280 assump_685
                  apply False.elim assump_289
                let assump_284 := assump_267 assump_684
                have assump_686 : True := by
                  apply True.intro
                let assump_293 := assump_284 assump_686
                apply False.elim assump_293
            case inr assump_263 =>
              cases assump_8
              case inl assump_299 =>
                apply Or.inl
                intro assump_303
                have assump_687 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_307 := assump_299 assump_687
                apply False.elim assump_307
              case inr assump_300 =>
                apply Or.inl
                intro assump_313
                have assump_688 : (p7 → False) := by
                  intro assump_318
                  have assump_689 : p7 := by
                    exact assump_318
                  let assump_322 := assump_313 assump_689
                  apply False.elim assump_322
                let assump_317 := assump_300 assump_688
                have assump_690 : True := by
                  apply True.intro
                let assump_326 := assump_317 assump_690
                apply False.elim assump_326
  case inr assump_4 =>
    cases assump_1
    case intro assump_332 assump_333 =>
      cases assump_332
      case intro assump_334 assump_335 =>
        cases assump_334
        case inl assump_336 =>
          cases assump_336
          case inl assump_338 =>
            cases assump_335
            case inl assump_342 =>
              cases assump_333
              case inl assump_346 =>
                apply Or.inl
                intro assump_350
                have assump_691 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_354 := assump_346 assump_691
                apply False.elim assump_354
              case inr assump_347 =>
                apply Or.inl
                intro assump_360
                have assump_692 : (p7 → False) := by
                  intro assump_365
                  have assump_693 : p7 := by
                    exact assump_365
                  let assump_369 := assump_360 assump_693
                  apply False.elim assump_369
                let assump_364 := assump_347 assump_692
                have assump_694 : True := by
                  apply True.intro
                let assump_373 := assump_364 assump_694
                apply False.elim assump_373
            case inr assump_343 =>
              cases assump_343
              case inl assump_377 =>
                cases assump_333
                case inl assump_381 =>
                  apply Or.inl
                  intro assump_385
                  have assump_695 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_389 := assump_381 assump_695
                  apply False.elim assump_389
                case inr assump_382 =>
                  apply Or.inl
                  intro assump_395
                  have assump_696 : (p7 → False) := by
                    intro assump_400
                    have assump_697 : p7 := by
                      exact assump_400
                    let assump_404 := assump_395 assump_697
                    apply False.elim assump_404
                  let assump_399 := assump_382 assump_696
                  have assump_698 : True := by
                    apply True.intro
                  let assump_408 := assump_399 assump_698
                  apply False.elim assump_408
              case inr assump_378 =>
                cases assump_333
                case inl assump_414 =>
                  apply Or.inl
                  intro assump_418
                  have assump_699 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_422 := assump_414 assump_699
                  apply False.elim assump_422
                case inr assump_415 =>
                  apply Or.inl
                  intro assump_428
                  have assump_700 : (p7 → False) := by
                    intro assump_433
                    have assump_701 : p7 := by
                      exact assump_433
                    let assump_437 := assump_428 assump_701
                    apply False.elim assump_437
                  let assump_432 := assump_415 assump_700
                  have assump_702 : True := by
                    apply True.intro
                  let assump_441 := assump_432 assump_702
                  apply False.elim assump_441
          case inr assump_339 =>
            cases assump_335
            case inl assump_447 =>
              cases assump_333
              case inl assump_451 =>
                apply Or.inl
                intro assump_455
                have assump_703 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_459 := assump_451 assump_703
                apply False.elim assump_459
              case inr assump_452 =>
                apply Or.inl
                intro assump_465
                have assump_704 : (p7 → False) := by
                  intro assump_470
                  have assump_705 : p7 := by
                    exact assump_470
                  let assump_474 := assump_465 assump_705
                  apply False.elim assump_474
                let assump_469 := assump_452 assump_704
                have assump_706 : True := by
                  apply True.intro
                let assump_478 := assump_469 assump_706
                apply False.elim assump_478
            case inr assump_448 =>
              cases assump_448
              case inl assump_482 =>
                cases assump_333
                case inl assump_486 =>
                  apply Or.inl
                  intro assump_490
                  have assump_707 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_494 := assump_486 assump_707
                  apply False.elim assump_494
                case inr assump_487 =>
                  apply Or.inl
                  intro assump_500
                  have assump_708 : (p7 → False) := by
                    intro assump_505
                    have assump_709 : p7 := by
                      exact assump_505
                    let assump_509 := assump_500 assump_709
                    apply False.elim assump_509
                  let assump_504 := assump_487 assump_708
                  have assump_710 : True := by
                    apply True.intro
                  let assump_513 := assump_504 assump_710
                  apply False.elim assump_513
              case inr assump_483 =>
                cases assump_333
                case inl assump_519 =>
                  apply Or.inl
                  intro assump_523
                  have assump_711 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_527 := assump_519 assump_711
                  apply False.elim assump_527
                case inr assump_520 =>
                  apply Or.inl
                  intro assump_533
                  have assump_712 : (p7 → False) := by
                    intro assump_538
                    have assump_713 : p7 := by
                      exact assump_538
                    let assump_542 := assump_533 assump_713
                    apply False.elim assump_542
                  let assump_537 := assump_520 assump_712
                  have assump_714 : True := by
                    apply True.intro
                  let assump_546 := assump_537 assump_714
                  apply False.elim assump_546
        case inr assump_337 =>
          cases assump_335
          case inl assump_552 =>
            cases assump_333
            case inl assump_556 =>
              apply Or.inl
              intro assump_560
              have assump_715 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_564 := assump_556 assump_715
              apply False.elim assump_564
            case inr assump_557 =>
              apply Or.inl
              intro assump_570
              have assump_716 : (p7 → False) := by
                intro assump_575
                have assump_717 : p7 := by
                  exact assump_575
                let assump_579 := assump_570 assump_717
                apply False.elim assump_579
              let assump_574 := assump_557 assump_716
              have assump_718 : True := by
                apply True.intro
              let assump_583 := assump_574 assump_718
              apply False.elim assump_583
          case inr assump_553 =>
            cases assump_553
            case inl assump_587 =>
              cases assump_333
              case inl assump_591 =>
                apply Or.inl
                intro assump_595
                have assump_719 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_599 := assump_591 assump_719
                apply False.elim assump_599
              case inr assump_592 =>
                apply Or.inl
                intro assump_605
                have assump_720 : (p7 → False) := by
                  intro assump_610
                  have assump_721 : p7 := by
                    exact assump_610
                  let assump_614 := assump_605 assump_721
                  apply False.elim assump_614
                let assump_609 := assump_592 assump_720
                have assump_722 : True := by
                  apply True.intro
                let assump_618 := assump_609 assump_722
                apply False.elim assump_618
            case inr assump_588 =>
              cases assump_333
              case inl assump_624 =>
                apply Or.inl
                intro assump_628
                have assump_723 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_632 := assump_624 assump_723
                apply False.elim assump_632
              case inr assump_625 =>
                apply Or.inl
                intro assump_638
                have assump_724 : (p7 → False) := by
                  intro assump_643
                  have assump_725 : p7 := by
                    exact assump_643
                  let assump_647 := assump_638 assump_725
                  apply False.elim assump_647
                let assump_642 := assump_625 assump_724
                have assump_726 : True := by
                  apply True.intro
                let assump_651 := assump_642 assump_726
                apply False.elim assump_651


variable (p0 p2 p1 p4 p6 p3 p5 : Prop)
theorem file64_27671 : (((((p0 ∧ False) → False) → False) ∧ (((True ∨ p1) ∨ (p5 ∧ True)) → ((p2 ∧ False) ∨ (p3 → False)))) → ((((False → True) ∨ (p4 → False)) ∧ ((p5 ∧ p5) → (p4 → p5))) ∧ (((p2 → False) → (p6 → True)) ∨ ((p0 ∨ p2) ∧ (p6 ∧ p0))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply True.intro
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    cases assump_1
    case intro assump_19 assump_20 =>
      exact assump_14
  cases assump_1
  case intro assump_25 assump_26 =>
    apply Or.inl
    intro assump_31
    intro assump_32
    apply True.intro


variable (p2 p3 p6 p1 p0 p7 p4 : Prop)
theorem file64_28423 : ((((((p1 → False) → False) ∨ ((False → False) ∨ (p3 → False))) → (((p3 ∨ False) → False) → False)) ∧ ((((p2 → True) ∧ (p3 ∨ p7)) → ((p0 ∧ p1) ∨ (p4 ∨ p3))) ∧ (((True → False) → (p0 ∨ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((True → False) → (p0 ∨ p6)) := by
        intro assump_13
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_13 assump_24
        apply False.elim assump_16
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p1 p2 p6 p4 : Prop)
theorem file64_29114 : (((((p1 → p1) → False) ∧ ((p6 → True) ∧ (p2 ∨ True))) ∧ (((False ∨ False) ∨ (p6 → p1)) ∨ ((p4 ∧ p4) ∨ (p2 → p6)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_13
        case inl assump_16 =>
          cases assump_7
          case inl assump_20 =>
            cases assump_20
            case inl assump_22 =>
              cases assump_22
              case inl assump_24 =>
                apply False.elim assump_24
              case inr assump_25 =>
                apply False.elim assump_25
            case inr assump_23 =>
              have assump_126 : (p1 → p1) := by
                intro assump_36
                exact assump_36
              let assump_35 := assump_8 assump_126
              apply False.elim assump_35
          case inr assump_21 =>
            cases assump_21
            case inl assump_42 =>
              cases assump_42
              case intro assump_44 assump_45 =>
                have assump_127 : (p1 → p1) := by
                  intro assump_55
                  exact assump_55
                let assump_54 := assump_8 assump_127
                apply False.elim assump_54
            case inr assump_43 =>
              have assump_128 : (p1 → p1) := by
                intro assump_68
                exact assump_68
              let assump_67 := assump_8 assump_128
              apply False.elim assump_67
        case inr assump_17 =>
          cases assump_7
          case inl assump_76 =>
            cases assump_76
            case inl assump_78 =>
              cases assump_78
              case inl assump_80 =>
                apply False.elim assump_80
              case inr assump_81 =>
                apply False.elim assump_81
            case inr assump_79 =>
              have assump_129 : (p1 → p1) := by
                intro assump_91
                exact assump_91
              let assump_90 := assump_8 assump_129
              apply False.elim assump_90
          case inr assump_77 =>
            cases assump_77
            case inl assump_97 =>
              cases assump_97
              case intro assump_99 assump_100 =>
                have assump_130 : (p1 → p1) := by
                  intro assump_109
                  exact assump_109
                let assump_108 := assump_8 assump_130
                apply False.elim assump_108
            case inr assump_98 =>
              have assump_131 : (p1 → p1) := by
                intro assump_120
                exact assump_120
              let assump_119 := assump_8 assump_131
              apply False.elim assump_119


variable (p2 p4 p0 p1 p5 p6 p7 : Prop)
theorem file64_31922 : (((((p4 → False) ∨ (p2 ∧ p5)) → False) ∨ (((p2 → False) ∨ (p2 ∨ p7)) ∨ ((p1 → False) → (p5 ∧ p5)))) → ((((True → False) → False) ∧ ((False ∧ p1) → (p5 ∧ p0))) ∨ (((False ∨ p6) → False) ∧ ((p4 → False) → (p6 → True))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply And.intro
    intro assump_6
    have assump_100 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_100
    apply False.elim assump_9
    intro assump_13
    apply And.intro
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
    cases assump_13
    case intro assump_18 assump_19 =>
      apply False.elim assump_18
  case inr assump_3 =>
    cases assump_3
    case inl assump_22 =>
      cases assump_22
      case inl assump_24 =>
        apply Or.inl
        apply And.intro
        intro assump_28
        have assump_101 : True := by
          apply True.intro
        let assump_31 := assump_28 assump_101
        apply False.elim assump_31
        intro assump_35
        apply And.intro
        cases assump_35
        case intro assump_36 assump_37 =>
          apply False.elim assump_36
        cases assump_35
        case intro assump_40 assump_41 =>
          apply False.elim assump_40
      case inr assump_25 =>
        cases assump_25
        case inl assump_44 =>
          apply Or.inl
          apply And.intro
          intro assump_48
          have assump_102 : True := by
            apply True.intro
          let assump_51 := assump_48 assump_102
          apply False.elim assump_51
          intro assump_55
          apply And.intro
          cases assump_55
          case intro assump_56 assump_57 =>
            apply False.elim assump_56
          cases assump_55
          case intro assump_60 assump_61 =>
            apply False.elim assump_60
        case inr assump_45 =>
          apply Or.inl
          apply And.intro
          intro assump_66
          have assump_103 : True := by
            apply True.intro
          let assump_69 := assump_66 assump_103
          apply False.elim assump_69
          intro assump_73
          apply And.intro
          cases assump_73
          case intro assump_74 assump_75 =>
            apply False.elim assump_74
          cases assump_73
          case intro assump_78 assump_79 =>
            apply False.elim assump_78
    case inr assump_23 =>
      apply Or.inl
      apply And.intro
      intro assump_84
      have assump_104 : True := by
        apply True.intro
      let assump_87 := assump_84 assump_104
      apply False.elim assump_87
      intro assump_91
      apply And.intro
      cases assump_91
      case intro assump_92 assump_93 =>
        apply False.elim assump_92
      cases assump_91
      case intro assump_96 assump_97 =>
        apply False.elim assump_96


variable (p0 p4 p3 p7 p6 p1 p2 p5 : Prop)
theorem file64_34832 : (((((p1 ∧ p6) → False) → False) ∧ (((True → False) ∧ (p3 ∨ True)) ∧ ((p4 ∨ False) ∨ (p5 ∧ p7)))) → ((((True → p7) → (True ∨ p4)) ∨ ((p0 → False) → False)) → (((p1 → False) → False) → ((p2 → False) → (p2 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_2
  case inl assump_12 =>
    cases assump_1
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_23
          case inl assump_26 =>
            cases assump_21
            case inl assump_30 =>
              cases assump_30
              case inl assump_32 =>
                have assump_154 : True := by
                  apply True.intro
                let assump_38 := assump_22 assump_154
                apply False.elim assump_38
              case inr assump_33 =>
                apply False.elim assump_33
            case inr assump_31 =>
              cases assump_31
              case intro assump_44 assump_45 =>
                have assump_155 : True := by
                  apply True.intro
                let assump_53 := assump_22 assump_155
                apply False.elim assump_53
          case inr assump_27 =>
            cases assump_21
            case inl assump_59 =>
              cases assump_59
              case inl assump_61 =>
                have assump_156 : True := by
                  apply True.intro
                let assump_66 := assump_22 assump_156
                apply False.elim assump_66
              case inr assump_62 =>
                apply False.elim assump_62
            case inr assump_60 =>
              cases assump_60
              case intro assump_72 assump_73 =>
                have assump_157 : True := by
                  apply True.intro
                let assump_80 := assump_22 assump_157
                apply False.elim assump_80
  case inr assump_13 =>
    cases assump_1
    case intro assump_86 assump_87 =>
      cases assump_87
      case intro assump_90 assump_91 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          cases assump_93
          case inl assump_96 =>
            cases assump_91
            case inl assump_100 =>
              cases assump_100
              case inl assump_102 =>
                have assump_158 : True := by
                  apply True.intro
                let assump_108 := assump_92 assump_158
                apply False.elim assump_108
              case inr assump_103 =>
                apply False.elim assump_103
            case inr assump_101 =>
              cases assump_101
              case intro assump_114 assump_115 =>
                have assump_159 : True := by
                  apply True.intro
                let assump_123 := assump_92 assump_159
                apply False.elim assump_123
          case inr assump_97 =>
            cases assump_91
            case inl assump_129 =>
              cases assump_129
              case inl assump_131 =>
                have assump_160 : True := by
                  apply True.intro
                let assump_136 := assump_92 assump_160
                apply False.elim assump_136
              case inr assump_132 =>
                apply False.elim assump_132
            case inr assump_130 =>
              cases assump_130
              case intro assump_142 assump_143 =>
                have assump_161 : True := by
                  apply True.intro
                let assump_150 := assump_92 assump_161
                apply False.elim assump_150


variable (p1 p3 p2 p6 p5 p4 p0 p7 : Prop)
theorem file64_38538 : (((((p5 → False) → (p5 ∧ p5)) ∨ ((True ∧ True) → False)) → (((p6 ∧ False) → (p0 → p3)) ∨ ((p6 → p4) ∨ (p7 ∧ p2)))) ∨ ((((True → True) ∨ (p7 → False)) → False) → (((p1 ∧ p2) → False) ∨ ((p0 → False) ∧ (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  case inr assump_3 =>
    apply Or.inl
    intro assump_18
    intro assump_19
    cases assump_18
    case intro assump_22 assump_23 =>
      apply False.elim assump_23


variable (p4 p7 p3 p0 p2 p1 p5 : Prop)
theorem file64_39212 : (((((True ∨ p5) → (True → p3)) ∧ ((p5 ∨ p0) → (p0 ∧ p4))) ∧ (((p2 ∨ p4) ∨ (p5 → p0)) → False)) → ((((False ∨ p3) ∨ (p4 ∨ p3)) ∧ ((p7 → p1) ∨ (p3 ∧ p1))) ∨ (((p1 → False) ∧ (p2 ∨ p2)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inr
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_35 : ((p2 ∨ p4) ∨ (p5 → p0)) := by
            apply Or.inl
            apply Or.inl
            exact assump_17
          let assump_23 := assump_3 assump_35
          apply False.elim assump_23
        case inr assump_18 =>
          have assump_36 : ((p2 ∨ p4) ∨ (p5 → p0)) := by
            apply Or.inl
            apply Or.inl
            exact assump_18
          let assump_31 := assump_3 assump_36
          apply False.elim assump_31


variable (p3 p5 p2 p1 : Prop)
theorem file64_40212 : (((((p5 ∨ p1) → (False ∨ True)) → False) ∧ (((p2 ∧ p2) → (p2 → p2)) ∨ ((p5 → False) ∧ (p1 ∨ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_58 : ((p5 ∨ p1) → (False ∨ True)) := by
        intro assump_12
        cases assump_12
        case inl assump_13 =>
          apply Or.inr
          apply True.intro
        case inr assump_14 =>
          apply Or.inr
          apply True.intro
      let assump_11 := assump_2 assump_58
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_22 assump_23 =>
        cases assump_23
        case inl assump_26 =>
          have assump_59 : ((p5 ∨ p1) → (False ∨ True)) := by
            intro assump_33
            cases assump_33
            case inl assump_34 =>
              apply Or.inr
              apply True.intro
            case inr assump_35 =>
              apply Or.inr
              apply True.intro
          let assump_32 := assump_2 assump_59
          apply False.elim assump_32
        case inr assump_27 =>
          have assump_60 : ((p5 ∨ p1) → (False ∨ True)) := by
            intro assump_48
            cases assump_48
            case inl assump_49 =>
              apply Or.inr
              apply True.intro
            case inr assump_50 =>
              apply Or.inr
              apply True.intro
          let assump_47 := assump_2 assump_60
          apply False.elim assump_47


variable (p1 p5 p7 p3 p6 p0 p4 p2 : Prop)
theorem file64_41785 : (((((p5 → False) ∨ (True → False)) ∧ ((True → p1) ∨ (p0 → False))) ∧ (((p4 ∧ p7) → False) ∧ ((False → p2) → False))) → ((((p3 ∨ p1) ∨ (p1 ∨ p5)) → ((p6 ∨ p5) ∨ (p6 → False))) ∧ (((False ∨ p1) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case inl assump_13 =>
            cases assump_12
            case inl assump_17 =>
              cases assump_10
              case intro assump_21 assump_22 =>
                apply Or.inr
                intro assump_27
                have assump_410 : (False → p2) := by
                  intro assump_32
                  apply False.elim assump_32
                let assump_31 := assump_22 assump_410
                apply False.elim assump_31
            case inr assump_18 =>
              cases assump_10
              case intro assump_40 assump_41 =>
                apply Or.inr
                intro assump_46
                have assump_411 : (False → p2) := by
                  intro assump_51
                  apply False.elim assump_51
                let assump_50 := assump_41 assump_411
                apply False.elim assump_50
          case inr assump_14 =>
            cases assump_12
            case inl assump_59 =>
              cases assump_10
              case intro assump_63 assump_64 =>
                apply Or.inr
                intro assump_69
                have assump_412 : (False → p2) := by
                  intro assump_74
                  apply False.elim assump_74
                let assump_73 := assump_64 assump_412
                apply False.elim assump_73
            case inr assump_60 =>
              cases assump_10
              case intro assump_82 assump_83 =>
                apply Or.inr
                intro assump_88
                have assump_413 : (False → p2) := by
                  intro assump_93
                  apply False.elim assump_93
                let assump_92 := assump_83 assump_413
                apply False.elim assump_92
    case inr assump_6 =>
      cases assump_1
      case intro assump_101 assump_102 =>
        cases assump_101
        case intro assump_103 assump_104 =>
          cases assump_103
          case inl assump_105 =>
            cases assump_104
            case inl assump_109 =>
              cases assump_102
              case intro assump_113 assump_114 =>
                apply Or.inr
                intro assump_119
                have assump_414 : (False → p2) := by
                  intro assump_124
                  apply False.elim assump_124
                let assump_123 := assump_114 assump_414
                apply False.elim assump_123
            case inr assump_110 =>
              cases assump_102
              case intro assump_132 assump_133 =>
                apply Or.inr
                intro assump_138
                have assump_415 : (False → p2) := by
                  intro assump_143
                  apply False.elim assump_143
                let assump_142 := assump_133 assump_415
                apply False.elim assump_142
          case inr assump_106 =>
            cases assump_104
            case inl assump_151 =>
              cases assump_102
              case intro assump_155 assump_156 =>
                apply Or.inr
                intro assump_161
                have assump_416 : (False → p2) := by
                  intro assump_166
                  apply False.elim assump_166
                let assump_165 := assump_156 assump_416
                apply False.elim assump_165
            case inr assump_152 =>
              cases assump_102
              case intro assump_174 assump_175 =>
                apply Or.inr
                intro assump_180
                have assump_417 : (False → p2) := by
                  intro assump_185
                  apply False.elim assump_185
                let assump_184 := assump_175 assump_417
                apply False.elim assump_184
  case inr assump_4 =>
    cases assump_4
    case inl assump_191 =>
      cases assump_1
      case intro assump_195 assump_196 =>
        cases assump_195
        case intro assump_197 assump_198 =>
          cases assump_197
          case inl assump_199 =>
            cases assump_198
            case inl assump_203 =>
              cases assump_196
              case intro assump_207 assump_208 =>
                apply Or.inr
                intro assump_213
                have assump_418 : (False → p2) := by
                  intro assump_218
                  apply False.elim assump_218
                let assump_217 := assump_208 assump_418
                apply False.elim assump_217
            case inr assump_204 =>
              cases assump_196
              case intro assump_226 assump_227 =>
                apply Or.inr
                intro assump_232
                have assump_419 : (False → p2) := by
                  intro assump_237
                  apply False.elim assump_237
                let assump_236 := assump_227 assump_419
                apply False.elim assump_236
          case inr assump_200 =>
            cases assump_198
            case inl assump_245 =>
              cases assump_196
              case intro assump_249 assump_250 =>
                apply Or.inr
                intro assump_255
                have assump_420 : (False → p2) := by
                  intro assump_260
                  apply False.elim assump_260
                let assump_259 := assump_250 assump_420
                apply False.elim assump_259
            case inr assump_246 =>
              cases assump_196
              case intro assump_268 assump_269 =>
                apply Or.inr
                intro assump_274
                have assump_421 : (False → p2) := by
                  intro assump_279
                  apply False.elim assump_279
                let assump_278 := assump_269 assump_421
                apply False.elim assump_278
    case inr assump_192 =>
      cases assump_1
      case intro assump_287 assump_288 =>
        cases assump_287
        case intro assump_289 assump_290 =>
          cases assump_289
          case inl assump_291 =>
            cases assump_290
            case inl assump_295 =>
              cases assump_288
              case intro assump_299 assump_300 =>
                apply Or.inl
                apply Or.inr
                exact assump_192
            case inr assump_296 =>
              cases assump_288
              case intro assump_307 assump_308 =>
                apply Or.inl
                apply Or.inr
                exact assump_192
          case inr assump_292 =>
            cases assump_290
            case inl assump_315 =>
              cases assump_288
              case intro assump_319 assump_320 =>
                apply Or.inl
                apply Or.inr
                exact assump_192
            case inr assump_316 =>
              cases assump_288
              case intro assump_327 assump_328 =>
                apply Or.inl
                apply Or.inr
                exact assump_192
  intro assump_333
  cases assump_1
  case intro assump_336 assump_337 =>
    cases assump_336
    case intro assump_338 assump_339 =>
      cases assump_338
      case inl assump_340 =>
        cases assump_339
        case inl assump_344 =>
          cases assump_337
          case intro assump_348 assump_349 =>
            have assump_422 : (False → p2) := by
              intro assump_355
              apply False.elim assump_355
            let assump_354 := assump_349 assump_422
            apply False.elim assump_354
        case inr assump_345 =>
          cases assump_337
          case intro assump_363 assump_364 =>
            have assump_423 : (False → p2) := by
              intro assump_370
              apply False.elim assump_370
            let assump_369 := assump_364 assump_423
            apply False.elim assump_369
      case inr assump_341 =>
        cases assump_339
        case inl assump_378 =>
          cases assump_337
          case intro assump_382 assump_383 =>
            have assump_424 : (False → p2) := by
              intro assump_389
              apply False.elim assump_389
            let assump_388 := assump_383 assump_424
            apply False.elim assump_388
        case inr assump_379 =>
          cases assump_337
          case intro assump_397 assump_398 =>
            have assump_425 : (False → p2) := by
              intro assump_404
              apply False.elim assump_404
            let assump_403 := assump_398 assump_425
            apply False.elim assump_403


variable (p5 p6 p7 p0 p4 p2 p1 : Prop)
theorem file64_50713 : (((((False → False) ∨ (False → False)) ∨ ((p5 → p1) → (False ∨ False))) ∧ (((False ∧ p4) → False) → False)) → ((((p7 → True) ∧ (p7 → p6)) → ((True ∨ p6) ∨ (p1 ∨ p6))) ∧ (((p6 → p5) → (True ∧ p2)) ∨ ((True ∧ p0) ∨ (p0 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_14 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_12 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  cases assump_1
  case intro assump_27 assump_28 =>
    cases assump_27
    case inl assump_29 =>
      cases assump_29
      case inl assump_31 =>
        apply Or.inl
        intro assump_37
        apply And.intro
        apply True.intro
        have assump_84 : ((False ∧ p4) → False) := by
          intro assump_42
          cases assump_42
          case intro assump_43 assump_44 =>
            apply False.elim assump_43
        let assump_41 := assump_28 assump_84
        apply False.elim assump_41
      case inr assump_32 =>
        apply Or.inl
        intro assump_54
        apply And.intro
        apply True.intro
        have assump_85 : ((False ∧ p4) → False) := by
          intro assump_59
          cases assump_59
          case intro assump_60 assump_61 =>
            apply False.elim assump_60
        let assump_58 := assump_28 assump_85
        apply False.elim assump_58
    case inr assump_30 =>
      apply Or.inl
      intro assump_71
      apply And.intro
      apply True.intro
      have assump_86 : ((False ∧ p4) → False) := by
        intro assump_76
        cases assump_76
        case intro assump_77 assump_78 =>
          apply False.elim assump_77
      let assump_75 := assump_28 assump_86
      apply False.elim assump_75


variable (p1 p4 p6 p5 p0 p7 p2 p3 : Prop)
theorem file64_52818 : (((((p1 → False) ∧ (True → False)) → False) ∨ (((p4 ∨ p1) → (p2 ∧ False)) → ((p3 → False) ∧ (p5 ∧ p7)))) ∨ ((((p5 → False) ∧ (True ∧ p6)) → False) → (((p1 → False) ∨ (p0 → p2)) ∨ ((p0 ∨ True) → (p2 ∧ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_16 : True := by
      apply True.intro
    let assump_12 := assump_7 assump_16
    apply False.elim assump_12


variable (p2 p6 p1 p0 p4 p5 : Prop)
theorem file64_53316 : (((((p2 → False) ∧ (p6 ∧ False)) → ((p4 ∨ p0) ∨ (p1 ∨ p2))) ∧ (((p6 ∨ p6) → (p6 → False)) ∨ ((p1 → False) → False))) → ((((p0 → False) ∧ (p5 ∧ False)) ∧ ((p2 → False) → False)) → (((True → p2) ∨ (p5 ∧ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  case inr assump_5 =>
    cases assump_5
    case intro assump_20 assump_21 =>
      cases assump_2
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_29
          case intro assump_32 assump_33 =>
            apply False.elim assump_33


variable (p0 p3 p1 p5 p7 p4 p6 p2 : Prop)
theorem file64_54231 : ((((((False ∧ p6) ∨ (p7 ∧ True)) → ((p0 ∨ p4) ∧ (p3 → p2))) ∧ (((False → False) ∧ (p1 → False)) ∧ ((p5 ∧ True) ∧ (p7 → False)))) ∧ ((((p1 ∨ p5) ∨ (p3 → False)) ∨ ((p1 ∨ p4) ∧ (p0 → False))) → False)) → False) := by
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
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_32 : (((p1 ∨ p5) ∨ (p3 → False)) ∨ ((p1 ∨ p4) ∧ (p0 → False))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_18
              let assump_28 := assump_3 assump_32
              apply False.elim assump_28


variable (p1 p5 p4 p6 p0 p2 p7 : Prop)
theorem file64_55204 : (((((False ∧ p7) ∧ (p0 → False)) → ((p4 → False) ∧ (p6 → False))) → (((False ∧ p1) ∨ (False ∧ p2)) → False)) ∨ ((((p2 → p4) ∨ (p2 ∧ p0)) → ((p7 ∧ p2) ∧ (p5 ∨ p2))) → (((False ∨ p6) → False) ∨ ((False → p6) ∧ (p2 → p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  case inr assump_4 =>
    cases assump_4
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p7 p0 p5 p6 p2 p3 p4 : Prop)
theorem file64_55782 : (((((p3 ∧ p7) → False) → ((p4 → False) ∨ (p6 → False))) → (((False → p7) → False) ∨ ((True ∨ p6) ∨ (p4 ∧ p6)))) → ((((p0 ∨ p6) ∧ (True ∧ p0)) ∧ ((p5 ∨ p2) → (p6 ∧ p0))) ∨ (((True ∧ False) ∨ (p0 ∧ False)) → False))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  case inr assump_6 =>
    cases assump_6
    case intro assump_13 assump_14 =>
      apply False.elim assump_14


variable (p5 p0 p7 p2 p6 : Prop)
theorem file64_56349 : ((((((p5 → p0) ∧ (True → False)) → False) → (((True ∧ p7) → False) → ((False → p5) ∨ (p2 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p5 → p0) ∧ (True → False)) → False) → (((True ∧ p7) → False) → ((False → p5) ∨ (p2 ∨ p6)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p2 p3 p6 : Prop)
theorem file64_56831 : (((((p6 ∨ p2) → False) → ((p3 ∨ p3) → (p6 → p2))) → False) → False) := by
  intro assump_1
  have assump_31 : (((p6 ∨ p2) → False) → ((p3 ∨ p3) → (p6 → p2))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      have assump_32 : (p6 ∨ p2) := by
        apply Or.inl
        exact assump_7
      let assump_16 := assump_5 assump_32
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_33 : (p6 ∨ p2) := by
        apply Or.inl
        exact assump_7
      let assump_24 := assump_5 assump_33
      apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p5 p3 p6 p1 p2 p4 p0 : Prop)
theorem file64_57567 : (((((p0 → p5) ∨ (p2 → False)) ∧ ((False ∨ p3) → (p3 ∧ p3))) ∨ (((p5 ∨ p2) ∨ (p6 ∧ p5)) → False)) → ((((p4 ∨ p1) ∧ (p6 → False)) → False) → (((True ∨ p1) → False) → False))) := by
  intro assump_28
  intro assump_29
  intro assump_30
  cases assump_28
  case inl assump_35 =>
    cases assump_35
    case intro assump_37 assump_38 =>
      cases assump_37
      case inl assump_39 =>
        have assump_71 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_48 := assump_30 assump_71
        apply False.elim assump_48
      case inr assump_40 =>
        have assump_72 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_59 := assump_30 assump_72
        apply False.elim assump_59
  case inr assump_36 =>
    have assump_73 : (True ∨ p1) := by
      apply Or.inl
      apply True.intro
    let assump_67 := assump_30 assump_73
    apply False.elim assump_67


variable (p5 p1 p0 p7 : Prop)
theorem file64_58555 : ((((((p0 → p0) → False) → ((False ∨ False) ∨ (p0 ∨ p7))) ∨ (((p5 ∨ p5) → (p1 → True)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 → p0) → False) → ((False ∨ False) ∨ (p0 ∨ p7))) ∨ (((p5 ∨ p5) → (p1 → True)) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (p0 → p0) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p3 p6 p4 p2 p5 p0 : Prop)
theorem file64_59123 : (((((True → False) → (False → False)) ∨ ((p4 ∧ p6) → False)) ∧ (((p5 → False) ∨ (True ∨ p4)) → ((p0 ∨ p1) ∨ (p3 → p3)))) ∨ ((((p2 → False) ∨ (p5 ∨ p1)) → False) ∧ (((p6 → False) ∨ (p1 → False)) → ((False → p4) → False)))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    apply Or.inr
    intro assump_10
    exact assump_10
  case inr assump_7 =>
    cases assump_7
    case inl assump_13 =>
      apply Or.inr
      intro assump_17
      exact assump_17
    case inr assump_14 =>
      apply Or.inr
      intro assump_22
      exact assump_22


variable (p7 p2 p0 p4 p6 p3 p1 : Prop)
theorem file64_59858 : (((((True → p2) → (p2 ∧ True)) → False) ∧ (((p4 → p7) ∨ (p0 ∨ p6)) ∨ ((False ∧ p1) → False))) → ((((p7 → p7) ∨ (p3 → p7)) → ((True → p2) ∧ (p4 → False))) ∧ (((p0 → False) ∨ (False ∧ p6)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          have assump_322 : ((True → p2) → (p2 ∧ True)) := by
            intro assump_22
            apply And.intro
            have assump_323 : True := by
              apply True.intro
            let assump_25 := assump_22 assump_323
            exact assump_25
            apply True.intro
          let assump_21 := assump_10 assump_322
          apply False.elim assump_21
        case inr assump_17 =>
          cases assump_17
          case inl assump_30 =>
            have assump_324 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_36
              apply And.intro
              have assump_325 : True := by
                apply True.intro
              let assump_39 := assump_36 assump_325
              exact assump_39
              apply True.intro
            let assump_35 := assump_10 assump_324
            apply False.elim assump_35
          case inr assump_31 =>
            have assump_326 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_48
              apply And.intro
              have assump_327 : True := by
                apply True.intro
              let assump_51 := assump_48 assump_327
              exact assump_51
              apply True.intro
            let assump_47 := assump_10 assump_326
            apply False.elim assump_47
      case inr assump_15 =>
        have assump_328 : ((True → p2) → (p2 ∧ True)) := by
          intro assump_60
          apply And.intro
          have assump_329 : True := by
            apply True.intro
          let assump_63 := assump_60 assump_329
          exact assump_63
          apply True.intro
        let assump_59 := assump_10 assump_328
        apply False.elim assump_59
  case inr assump_7 =>
    cases assump_1
    case intro assump_70 assump_71 =>
      cases assump_71
      case inl assump_74 =>
        cases assump_74
        case inl assump_76 =>
          have assump_330 : ((True → p2) → (p2 ∧ True)) := by
            intro assump_82
            apply And.intro
            have assump_331 : True := by
              apply True.intro
            let assump_85 := assump_82 assump_331
            exact assump_85
            apply True.intro
          let assump_81 := assump_70 assump_330
          apply False.elim assump_81
        case inr assump_77 =>
          cases assump_77
          case inl assump_90 =>
            have assump_332 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_96
              apply And.intro
              have assump_333 : True := by
                apply True.intro
              let assump_99 := assump_96 assump_333
              exact assump_99
              apply True.intro
            let assump_95 := assump_70 assump_332
            apply False.elim assump_95
          case inr assump_91 =>
            have assump_334 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_108
              apply And.intro
              have assump_335 : True := by
                apply True.intro
              let assump_111 := assump_108 assump_335
              exact assump_111
              apply True.intro
            let assump_107 := assump_70 assump_334
            apply False.elim assump_107
      case inr assump_75 =>
        have assump_336 : ((True → p2) → (p2 ∧ True)) := by
          intro assump_120
          apply And.intro
          have assump_337 : True := by
            apply True.intro
          let assump_123 := assump_120 assump_337
          exact assump_123
          apply True.intro
        let assump_119 := assump_70 assump_336
        apply False.elim assump_119
  intro assump_128
  cases assump_2
  case inl assump_131 =>
    cases assump_1
    case intro assump_135 assump_136 =>
      cases assump_136
      case inl assump_139 =>
        cases assump_139
        case inl assump_141 =>
          have assump_338 : ((True → p2) → (p2 ∧ True)) := by
            intro assump_148
            apply And.intro
            have assump_339 : True := by
              apply True.intro
            let assump_151 := assump_148 assump_339
            exact assump_151
            apply True.intro
          let assump_147 := assump_135 assump_338
          apply False.elim assump_147
        case inr assump_142 =>
          cases assump_142
          case inl assump_156 =>
            have assump_340 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_162
              apply And.intro
              have assump_341 : True := by
                apply True.intro
              let assump_165 := assump_162 assump_341
              exact assump_165
              apply True.intro
            let assump_161 := assump_135 assump_340
            apply False.elim assump_161
          case inr assump_157 =>
            have assump_342 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_174
              apply And.intro
              have assump_343 : True := by
                apply True.intro
              let assump_177 := assump_174 assump_343
              exact assump_177
              apply True.intro
            let assump_173 := assump_135 assump_342
            apply False.elim assump_173
      case inr assump_140 =>
        have assump_344 : ((True → p2) → (p2 ∧ True)) := by
          intro assump_186
          apply And.intro
          have assump_345 : True := by
            apply True.intro
          let assump_189 := assump_186 assump_345
          exact assump_189
          apply True.intro
        let assump_185 := assump_135 assump_344
        apply False.elim assump_185
  case inr assump_132 =>
    cases assump_1
    case intro assump_196 assump_197 =>
      cases assump_197
      case inl assump_200 =>
        cases assump_200
        case inl assump_202 =>
          have assump_346 : ((True → p2) → (p2 ∧ True)) := by
            intro assump_209
            apply And.intro
            have assump_347 : True := by
              apply True.intro
            let assump_212 := assump_209 assump_347
            exact assump_212
            apply True.intro
          let assump_208 := assump_196 assump_346
          apply False.elim assump_208
        case inr assump_203 =>
          cases assump_203
          case inl assump_217 =>
            have assump_348 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_223
              apply And.intro
              have assump_349 : True := by
                apply True.intro
              let assump_226 := assump_223 assump_349
              exact assump_226
              apply True.intro
            let assump_222 := assump_196 assump_348
            apply False.elim assump_222
          case inr assump_218 =>
            have assump_350 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_235
              apply And.intro
              have assump_351 : True := by
                apply True.intro
              let assump_238 := assump_235 assump_351
              exact assump_238
              apply True.intro
            let assump_234 := assump_196 assump_350
            apply False.elim assump_234
      case inr assump_201 =>
        have assump_352 : ((True → p2) → (p2 ∧ True)) := by
          intro assump_247
          apply And.intro
          have assump_353 : True := by
            apply True.intro
          let assump_250 := assump_247 assump_353
          exact assump_250
          apply True.intro
        let assump_246 := assump_196 assump_352
        apply False.elim assump_246
  intro assump_255
  cases assump_255
  case inl assump_256 =>
    cases assump_1
    case intro assump_260 assump_261 =>
      cases assump_261
      case inl assump_264 =>
        cases assump_264
        case inl assump_266 =>
          have assump_354 : ((True → p2) → (p2 ∧ True)) := by
            intro assump_272
            apply And.intro
            have assump_355 : True := by
              apply True.intro
            let assump_275 := assump_272 assump_355
            exact assump_275
            apply True.intro
          let assump_271 := assump_260 assump_354
          apply False.elim assump_271
        case inr assump_267 =>
          cases assump_267
          case inl assump_280 =>
            have assump_356 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_286
              apply And.intro
              have assump_357 : True := by
                apply True.intro
              let assump_289 := assump_286 assump_357
              exact assump_289
              apply True.intro
            let assump_285 := assump_260 assump_356
            apply False.elim assump_285
          case inr assump_281 =>
            have assump_358 : ((True → p2) → (p2 ∧ True)) := by
              intro assump_298
              apply And.intro
              have assump_359 : True := by
                apply True.intro
              let assump_301 := assump_298 assump_359
              exact assump_301
              apply True.intro
            let assump_297 := assump_260 assump_358
            apply False.elim assump_297
      case inr assump_265 =>
        have assump_360 : ((True → p2) → (p2 ∧ True)) := by
          intro assump_310
          apply And.intro
          have assump_361 : True := by
            apply True.intro
          let assump_313 := assump_310 assump_361
          exact assump_313
          apply True.intro
        let assump_309 := assump_260 assump_360
        apply False.elim assump_309
  case inr assump_257 =>
    cases assump_257
    case intro assump_318 assump_319 =>
      apply False.elim assump_318


variable (p6 p5 p0 p4 p1 p3 : Prop)
theorem file64_69955 : (((((p5 → p5) ∨ (p6 → p4)) ∨ ((True ∧ p6) ∧ (p1 → p3))) → False) → ((((p3 → False) → False) → ((p0 ∨ p6) ∨ (False ∧ p0))) → (((False ∧ p5) → False) ∧ ((p4 → False) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  intro assump_8
  intro assump_9
  have assump_25 : (((p5 → p5) ∨ (p6 → p4)) ∨ ((True ∧ p6) ∧ (p1 → p3))) := by
    apply Or.inl
    apply Or.inl
    intro assump_19
    exact assump_19
  let assump_18 := assump_1 assump_25
  apply False.elim assump_18


variable (p3 p0 p5 p2 p1 p7 : Prop)
theorem file64_70608 : ((((((p5 → False) → (p2 → False)) → ((p1 → p3) ∧ (p3 → False))) → (((p2 → False) ∨ (p2 → p0)) → ((True ∨ p7) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p5 → False) → (p2 → False)) → ((p1 → p3) ∧ (p3 → False))) → (((p2 → False) ∨ (p2 → p0)) → ((True ∨ p7) ∨ (p2 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p6 p1 p5 p7 p4 p0 p3 : Prop)
theorem file64_71283 : (((((True ∧ p1) → (p5 → p6)) ∨ ((p5 → p0) → False)) ∧ (((False → False) → False) ∧ ((p7 ∧ True) → (True → False)))) → ((((p7 ∧ p5) → False) ∧ ((False ∨ p0) ∧ (p1 ∧ p4))) ∧ (((True → False) → (p3 ∧ p6)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          have assump_186 : (p7 ∧ True) := by
            apply And.intro
            exact assump_3
            apply True.intro
          let assump_21 := assump_16 assump_186
          have assump_187 : True := by
            apply True.intro
          let assump_22 := assump_21 assump_187
          apply False.elim assump_22
      case inr assump_12 =>
        cases assump_10
        case intro assump_28 assump_29 =>
          have assump_188 : (p7 ∧ True) := by
            apply And.intro
            exact assump_3
            apply True.intro
          let assump_34 := assump_29 assump_188
          have assump_189 : True := by
            apply True.intro
          let assump_35 := assump_34 assump_189
          apply False.elim assump_35
  apply And.intro
  cases assump_1
  case intro assump_39 assump_40 =>
    cases assump_39
    case inl assump_41 =>
      cases assump_40
      case intro assump_45 assump_46 =>
        have assump_190 : (False → False) := by
          intro assump_53
          apply False.elim assump_53
        let assump_52 := assump_45 assump_190
        apply False.elim assump_52
    case inr assump_42 =>
      cases assump_40
      case intro assump_61 assump_62 =>
        have assump_191 : (False → False) := by
          intro assump_69
          apply False.elim assump_69
        let assump_68 := assump_61 assump_191
        apply False.elim assump_68
  apply And.intro
  cases assump_1
  case intro assump_75 assump_76 =>
    cases assump_75
    case inl assump_77 =>
      cases assump_76
      case intro assump_81 assump_82 =>
        have assump_192 : (False → False) := by
          intro assump_89
          apply False.elim assump_89
        let assump_88 := assump_81 assump_192
        apply False.elim assump_88
    case inr assump_78 =>
      cases assump_76
      case intro assump_97 assump_98 =>
        have assump_193 : (False → False) := by
          intro assump_105
          apply False.elim assump_105
        let assump_104 := assump_97 assump_193
        apply False.elim assump_104
  cases assump_1
  case intro assump_111 assump_112 =>
    cases assump_111
    case inl assump_113 =>
      cases assump_112
      case intro assump_117 assump_118 =>
        have assump_194 : (False → False) := by
          intro assump_125
          apply False.elim assump_125
        let assump_124 := assump_117 assump_194
        apply False.elim assump_124
    case inr assump_114 =>
      cases assump_112
      case intro assump_133 assump_134 =>
        have assump_195 : (False → False) := by
          intro assump_141
          apply False.elim assump_141
        let assump_140 := assump_133 assump_195
        apply False.elim assump_140
  intro assump_147
  cases assump_1
  case intro assump_150 assump_151 =>
    cases assump_150
    case inl assump_152 =>
      cases assump_151
      case intro assump_156 assump_157 =>
        have assump_196 : (False → False) := by
          intro assump_164
          apply False.elim assump_164
        let assump_163 := assump_156 assump_196
        apply False.elim assump_163
    case inr assump_153 =>
      cases assump_151
      case intro assump_172 assump_173 =>
        have assump_197 : (False → False) := by
          intro assump_180
          apply False.elim assump_180
        let assump_179 := assump_172 assump_197
        apply False.elim assump_179


variable (p4 p2 p5 p6 p1 p0 : Prop)
theorem file64_75243 : ((((((p6 → p1) ∨ (p0 ∨ p4)) ∧ ((p0 ∧ p1) → (p1 ∧ p5))) → False) ∧ ((((p0 ∨ p2) ∧ (False → p4)) ∨ ((p2 ∧ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((p0 ∨ p2) ∧ (False → p4)) ∨ ((p2 ∧ p2) → False)) := by
      apply Or.inr
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        have assump_29 : (((p0 ∨ p2) ∧ (False → p4)) ∨ ((p2 ∧ p2) → False)) := by
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_11
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_3 assump_29
        apply False.elim assump_18
    let assump_8 := assump_3 assump_28
    apply False.elim assump_8


variable (p2 p5 p6 p7 p3 p0 p4 p1 : Prop)
theorem file64_76090 : (((((p5 → False) → (p7 → False)) ∨ ((p2 → p4) → (p5 → False))) ∧ (((p1 → p0) → False) ∧ ((p3 ∨ p6) → False))) → ((((p2 → p4) → False) → ((False → True) ∨ (p3 → p5))) ∨ (((p4 → p0) ∧ (p7 ∨ p5)) ∨ ((p2 ∨ p6) ∧ (p4 → p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_14
        apply Or.inl
        intro assump_17
        apply True.intro
    case inr assump_5 =>
      cases assump_3
      case intro assump_20 assump_21 =>
        apply Or.inl
        intro assump_26
        apply Or.inl
        intro assump_29
        apply True.intro


variable (p5 p2 p6 p1 p7 p0 p4 p3 : Prop)
theorem file64_76871 : (((((p3 ∧ p0) ∨ (p6 ∨ p7)) → ((False → False) ∧ (False → p5))) → False) → ((((p2 → False) ∨ (p0 → False)) → False) ∨ (((p1 ∨ p3) → (p2 ∨ p4)) ∧ ((p6 ∨ p3) ∨ (p5 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_35 : (((p3 ∧ p0) ∨ (p6 ∨ p7)) → ((False → False) ∧ (False → p5))) := by
      intro assump_11
      apply And.intro
      intro assump_12
      apply False.elim assump_12
      intro assump_15
      apply False.elim assump_15
    let assump_10 := assump_1 assump_35
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_36 : (((p3 ∧ p0) ∨ (p6 ∨ p7)) → ((False → False) ∧ (False → p5))) := by
      intro assump_25
      apply And.intro
      intro assump_26
      apply False.elim assump_26
      intro assump_29
      apply False.elim assump_29
    let assump_24 := assump_1 assump_36
    apply False.elim assump_24


variable (p6 p0 : Prop)
theorem file64_77837 : (((((False ∧ p0) → False) ∨ ((p6 → False) → False)) → False) → False) := by
  intro assump_25
  have assump_37 : (((False ∧ p0) → False) ∨ ((p6 → False) → False)) := by
    apply Or.inl
    intro assump_29
    cases assump_29
    case intro assump_30 assump_31 =>
      apply False.elim assump_30
  let assump_28 := assump_25 assump_37
  apply False.elim assump_28


variable (p0 p5 p3 p1 p7 p4 p6 p2 : Prop)
theorem file64_78268 : (((((p0 ∧ p0) ∧ (p4 → p3)) → ((p5 ∨ p0) ∨ (False ∧ p4))) ∨ (((p1 ∧ p0) ∧ (p7 ∨ p2)) → False)) ∨ ((((p1 → False) ∨ (False → False)) ∨ ((p7 ∨ p6) ∧ (False → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inr
      exact assump_5


variable (p1 p5 p2 p7 p4 p0 p6 : Prop)
theorem file64_78723 : (((((p6 ∨ False) ∨ (p4 ∧ False)) → ((p2 → False) → False)) → (((p0 ∨ False) ∨ (p5 ∧ p1)) ∨ ((True → False) → False))) ∧ ((((True → False) ∧ (p4 → False)) → ((False ∨ p6) ∨ (p4 ∨ p7))) ∨ (((p6 ∧ p2) → (p0 → False)) → ((p6 ∨ p7) ∨ (p6 → False))))) := by
  apply And.intro
  intro assump_5
  apply Or.inr
  intro assump_8
  have assump_27 : True := by
    apply True.intro
  let assump_11 := assump_8 assump_27
  apply False.elim assump_11
  apply Or.inl
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    have assump_28 : True := by
      apply True.intro
    let assump_23 := assump_16 assump_28
    apply False.elim assump_23


variable (p5 p1 : Prop)
theorem file64_79422 : ((((((p1 ∨ p5) ∨ (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 ∨ p5) ∨ (False → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p1 ∨ p5) ∨ (False → False)) := by
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p1 p3 p7 p5 p4 : Prop)
theorem file64_79932 : (((((True → False) → (p3 → False)) ∨ ((p7 ∧ p1) ∧ (p2 ∧ p3))) → False) → ((((p5 ∨ p2) → (True ∧ p2)) ∧ ((p3 → p7) ∨ (p1 → p4))) ∨ (((p2 → False) → (p4 → p4)) ∨ ((False → False) ∧ (p4 ∨ p1))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  apply And.intro
  apply True.intro
  cases assump_4
  case inl assump_5 =>
    have assump_44 : (((True → False) → (p3 → False)) ∨ ((p7 ∧ p1) ∧ (p2 ∧ p3))) := by
      apply Or.inl
      intro assump_11
      intro assump_12
      have assump_45 : True := by
        apply True.intro
      let assump_17 := assump_11 assump_45
      apply False.elim assump_17
    let assump_10 := assump_1 assump_44
    apply False.elim assump_10
  case inr assump_6 =>
    exact assump_6
  apply Or.inl
  intro assump_26
  have assump_46 : (((True → False) → (p3 → False)) ∨ ((p7 ∧ p1) ∧ (p2 ∧ p3))) := by
    apply Or.inl
    intro assump_31
    intro assump_32
    have assump_47 : True := by
      apply True.intro
    let assump_37 := assump_31 assump_47
    apply False.elim assump_37
  let assump_30 := assump_1 assump_46
  apply False.elim assump_30


variable (p5 p7 p4 p1 p6 p0 : Prop)
theorem file64_81102 : (((((False ∧ p5) → False) → False) → (((p1 → p1) ∧ (p0 ∧ p6)) → ((p6 ∨ p4) ∨ (p6 ∨ True)))) ∨ ((((p5 ∧ p7) ∨ (True → p7)) ∧ ((p1 ∨ True) ∧ (p7 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply Or.inl
      apply Or.inl
      exact assump_8


variable (p7 p5 p4 p6 p1 : Prop)
theorem file64_81542 : ((((((p4 ∧ False) ∨ (p7 ∧ False)) ∨ ((p5 → p7) → (p5 ∨ True))) → (((True → False) → (True ∨ p4)) ∨ ((p6 → p5) → (True ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p4 ∧ False) ∨ (p7 ∧ False)) ∨ ((p5 → p7) → (p5 ∨ True))) → (((True → False) → (True ∨ p4)) ∨ ((p6 → p5) → (True ∧ p1)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_9 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
    case inr assump_7 =>
      apply Or.inl
      intro assump_24
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p5 p6 p7 p1 p4 p2 p3 : Prop)
theorem file64_82438 : (((((p7 ∧ p7) → False) → False) ∧ (((p6 → False) → (p2 → p4)) → False)) → ((((p2 → False) → (p4 → p5)) → ((p3 → True) ∨ (False → p1))) ∨ (((p3 → False) → False) → ((p4 → True) ∧ (p4 ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply Or.inl
    intro assump_11
    apply True.intro


variable (p6 p5 p7 p1 p3 p0 p4 : Prop)
theorem file64_82861 : (((((p0 ∨ True) ∧ (False → p6)) → ((False ∧ p3) → (p4 → False))) → (((p1 → True) → False) → ((p6 → p1) → (p5 ∧ True)))) → ((((p5 ∧ p0) ∧ (p6 ∨ p0)) ∧ ((p1 ∨ False) ∧ (False ∨ False))) → (((p0 → p1) → (p3 → p7)) ∨ ((p5 ∧ True) ∨ (p6 ∧ p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case inl assump_13 =>
          cases assump_4
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_18
              case inl assump_23 =>
                apply False.elim assump_23
              case inr assump_24 =>
                apply False.elim assump_24
            case inr assump_20 =>
              apply False.elim assump_20
        case inr assump_14 =>
          cases assump_4
          case intro assump_33 assump_34 =>
            cases assump_33
            case inl assump_35 =>
              cases assump_34
              case inl assump_39 =>
                apply False.elim assump_39
              case inr assump_40 =>
                apply False.elim assump_40
            case inr assump_36 =>
              apply False.elim assump_36


variable (p2 p6 p4 p1 p5 p3 : Prop)
theorem file64_84239 : ((((((False → False) → (True → False)) → ((p5 ∨ False) ∨ (p4 ∧ p3))) ∨ (((False ∨ p5) ∨ (p2 → p4)) ∨ ((p6 ∨ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → False) → (True → False)) → ((p5 ∨ False) ∨ (p4 ∧ p3))) ∨ (((False ∨ p5) ∨ (p2 → p4)) ∨ ((p6 ∨ p1) → False))) := by
    apply Or.inl
    intro assump_5
    have assump_20 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_20
    have assump_21 : True := by
      apply True.intro
    let assump_12 := assump_8 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p0 p2 p6 p3 p5 p7 p4 : Prop)
theorem file64_84977 : (((((p6 → True) ∨ (False ∧ p7)) → ((p4 ∨ p6) ∧ (p3 → p3))) → (((p1 → False) → (p4 → p2)) ∨ ((p6 ∨ p0) → (p1 ∨ p3)))) → ((((p4 ∧ False) ∧ (False ∨ True)) → False) ∨ (((False ∨ p6) ∨ (p6 → p4)) → ((p7 ∨ True) ∧ (p5 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p0 p1 p7 p2 p3 : Prop)
theorem file64_85453 : ((((((p2 ∧ p7) → False) → ((p3 → p1) ∧ (False → p2))) → (((False ∨ False) → (p0 ∧ p3)) ∨ ((p3 ∨ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p2 ∧ p7) → False) → ((p3 → p1) ∧ (False → p2))) → (((False ∨ False) → (p0 ∧ p3)) ∨ ((p3 ∨ p3) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    cases assump_8
    case inl assump_9 =>
      apply False.elim assump_9
    case inr assump_10 =>
      apply False.elim assump_10
    cases assump_8
    case inl assump_15 =>
      apply False.elim assump_15
    case inr assump_16 =>
      apply False.elim assump_16
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p4 p7 p0 p2 p5 p1 p3 : Prop)
theorem file64_86214 : ((((((True → False) ∨ (p0 → p5)) → ((True ∧ True) ∨ (p5 ∧ p0))) ∨ (((p7 ∧ p4) → False) → ((p3 ∧ p4) ∨ (p1 → False)))) → ((((p4 ∧ False) → False) → False) ∧ (((p2 → p2) ∨ (False → False)) → False))) → False) := by
  intro assump_1
  have assump_24 : ((((True → False) ∨ (p0 → p5)) → ((True ∧ True) ∨ (p5 ∧ p0))) ∨ (((p7 ∧ p4) → False) → ((p3 ∧ p4) ∨ (p1 → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply And.intro
      apply True.intro
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply And.intro
      apply True.intro
      apply True.intro
  let assump_4 := assump_1 assump_24
  let assump_12 := And.left assump_4
  have assump_25 : ((p4 ∧ False) → False) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_16
  let assump_13 := assump_12 assump_25
  apply False.elim assump_13


variable (p6 p7 : Prop)
theorem file64_87213 : (((((p6 ∧ p7) → (False → False)) → False) ∧ (((True → p7) → (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : ((True → p7) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p2 p7 p1 p3 p0 p5 p4 : Prop)
theorem file64_87650 : ((((((p7 → p3) → (False → True)) ∨ ((p0 → p2) → (p5 → False))) → False) ∧ ((((p7 → False) ∧ (False ∧ p7)) ∧ ((p7 ∨ p3) ∧ (p1 ∨ p1))) ∧ (((p2 ∨ p3) ∨ (p1 → p4)) ∨ ((p0 ∨ p2) ∧ (p4 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p1 p0 p7 p2 : Prop)
theorem file64_88264 : (((((True → False) → False) → False) → False) ∨ ((((True ∧ True) → False) ∨ ((False → p2) ∨ (p2 ∧ p0))) ∧ (((True ∧ p7) → (p1 → False)) → False))) := by
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


variable (p5 p0 p2 p4 p7 p3 p1 p6 : Prop)
theorem file64_88773 : ((((((p0 → p4) → False) → ((p4 ∧ p7) → (True → p6))) ∨ (((p6 ∨ p5) → (p2 → p6)) ∨ ((p7 → p0) → (p1 ∨ True)))) ∧ ((((p7 ∨ True) → False) → ((p0 ∨ p6) → (p3 ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_92 : (((p7 ∨ True) → False) → ((p0 ∨ p6) → (p3 ∨ p1))) := by
        intro assump_11
        intro assump_12
        cases assump_12
        case inl assump_13 =>
          have assump_93 : (p7 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_19 := assump_11 assump_93
          apply False.elim assump_19
        case inr assump_14 =>
          have assump_94 : (p7 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_27 := assump_11 assump_94
          apply False.elim assump_27
      let assump_10 := assump_3 assump_92
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_34 =>
        have assump_95 : (((p7 ∨ True) → False) → ((p0 ∨ p6) → (p3 ∨ p1))) := by
          intro assump_41
          intro assump_42
          cases assump_42
          case inl assump_43 =>
            have assump_96 : (p7 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_49 := assump_41 assump_96
            apply False.elim assump_49
          case inr assump_44 =>
            have assump_97 : (p7 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_57 := assump_41 assump_97
            apply False.elim assump_57
        let assump_40 := assump_3 assump_95
        apply False.elim assump_40
      case inr assump_35 =>
        have assump_98 : (((p7 ∨ True) → False) → ((p0 ∨ p6) → (p3 ∨ p1))) := by
          intro assump_69
          intro assump_70
          cases assump_70
          case inl assump_71 =>
            have assump_99 : (p7 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_77 := assump_69 assump_99
            apply False.elim assump_77
          case inr assump_72 =>
            have assump_100 : (p7 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_85 := assump_69 assump_100
            apply False.elim assump_85
        let assump_68 := assump_3 assump_98
        apply False.elim assump_68


variable (p4 p2 p7 p6 p0 p1 : Prop)
theorem file64_91265 : ((((((False → False) ∨ (p1 → False)) ∨ ((p4 → p0) ∧ (p6 → False))) ∨ (((p7 ∧ p1) ∨ (p0 ∧ p2)) → ((p1 ∨ p2) → (p7 → True)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (p1 → False)) ∨ ((p4 → p0) ∧ (p6 → False))) ∨ (((p7 ∧ p1) ∨ (p0 ∧ p2)) → ((p1 ∨ p2) → (p7 → True)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p4 p2 p3 : Prop)
theorem file64_91796 : (((((p1 → p3) → (p4 ∨ True)) ∨ ((p2 ∧ False) → False)) ∧ (((p2 → False) → (p1 → False)) ∧ ((p1 ∧ p2) ∧ (False ∧ p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              apply False.elim assump_20
    case inr assump_5 =>
      cases assump_3
      case intro assump_26 assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_31
            case intro assump_38 assump_39 =>
              apply False.elim assump_38


variable (p3 p2 : Prop)
theorem file64_92736 : (((((p2 → False) → (p3 → True)) ∨ ((p3 ∧ p3) → False)) → False) → False) := by
  intro assump_1
  have assump_10 : (((p2 → False) → (p3 → True)) ∨ ((p3 ∧ p3) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p7 p2 p6 p5 : Prop)
theorem file64_93105 : (((((p5 → False) ∧ (p2 → False)) → False) → False) → ((((False → False) ∨ (p5 → False)) ∨ ((p2 → False) → (True ∧ p2))) ∨ (((p7 → False) ∨ (p7 ∨ p7)) ∧ ((p6 → False) → (False → False))))) := by
  intro assump_48
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_51
  apply False.elim assump_51


variable (p3 p5 p4 p7 p1 p6 p0 : Prop)
theorem file64_93472 : (((((p0 → False) → False) → ((p3 ∨ p3) ∨ (p0 → p1))) → False) → ((((p3 ∧ True) ∧ (p6 → False)) → ((p7 ∨ p6) ∨ (p5 → p4))) ∨ (((p0 ∨ False) ∨ (p5 ∧ p7)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply Or.inr
      intro assump_15
      have assump_28 : (((p0 → False) → False) → ((p3 ∨ p3) ∨ (p0 → p1))) := by
        intro assump_22
        apply Or.inl
        apply Or.inl
        exact assump_7
      let assump_21 := assump_1 assump_28
      apply False.elim assump_21


variable (p3 p2 p0 p6 p7 p4 : Prop)
theorem file64_94141 : (((((p7 → False) ∧ (p0 ∨ True)) ∨ ((True ∨ False) → (p2 → False))) ∧ (((p4 → False) ∧ (p0 → p6)) ∧ ((p4 ∧ False) ∧ (p7 ∨ p4)))) → ((((p6 ∨ p4) → False) ∧ ((p7 ∧ p0) ∧ (p6 ∨ p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          cases assump_1
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                cases assump_24
                case inl assump_27 =>
                  cases assump_20
                  case intro assump_31 assump_32 =>
                    cases assump_31
                    case intro assump_33 assump_34 =>
                      cases assump_32
                      case intro assump_39 assump_40 =>
                        cases assump_39
                        case intro assump_41 assump_42 =>
                          apply False.elim assump_42
                case inr assump_28 =>
                  cases assump_20
                  case intro assump_49 assump_50 =>
                    cases assump_49
                    case intro assump_51 assump_52 =>
                      cases assump_50
                      case intro assump_57 assump_58 =>
                        cases assump_57
                        case intro assump_59 assump_60 =>
                          apply False.elim assump_60
            case inr assump_22 =>
              cases assump_20
              case intro assump_67 assump_68 =>
                cases assump_67
                case intro assump_69 assump_70 =>
                  cases assump_68
                  case intro assump_75 assump_76 =>
                    cases assump_75
                    case intro assump_77 assump_78 =>
                      apply False.elim assump_78
        case inr assump_16 =>
          cases assump_1
          case intro assump_85 assump_86 =>
            cases assump_85
            case inl assump_87 =>
              cases assump_87
              case intro assump_89 assump_90 =>
                cases assump_90
                case inl assump_93 =>
                  cases assump_86
                  case intro assump_97 assump_98 =>
                    cases assump_97
                    case intro assump_99 assump_100 =>
                      cases assump_98
                      case intro assump_105 assump_106 =>
                        cases assump_105
                        case intro assump_107 assump_108 =>
                          apply False.elim assump_108
                case inr assump_94 =>
                  cases assump_86
                  case intro assump_115 assump_116 =>
                    cases assump_115
                    case intro assump_117 assump_118 =>
                      cases assump_116
                      case intro assump_123 assump_124 =>
                        cases assump_123
                        case intro assump_125 assump_126 =>
                          apply False.elim assump_126
            case inr assump_88 =>
              cases assump_86
              case intro assump_133 assump_134 =>
                cases assump_133
                case intro assump_135 assump_136 =>
                  cases assump_134
                  case intro assump_141 assump_142 =>
                    cases assump_141
                    case intro assump_143 assump_144 =>
                      apply False.elim assump_144


variable (p4 p6 p3 p1 p7 p2 p5 : Prop)
theorem file64_97869 : (((((False ∨ p7) ∨ (p7 ∨ p6)) ∧ ((p1 ∧ p2) ∧ (True ∨ p3))) → (((p1 ∨ p3) ∧ (p4 ∧ False)) → ((p6 ∧ p3) → (p1 ∧ p4)))) ∨ ((((p4 ∨ p6) ∨ (p4 ∨ p6)) ∧ ((p5 → p2) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
      case inr assump_13 =>
        cases assump_11
        case intro assump_24 assump_25 =>
          apply False.elim assump_25
  cases assump_3
  case intro assump_30 assump_31 =>
    cases assump_2
    case intro assump_36 assump_37 =>
      cases assump_36
      case inl assump_38 =>
        cases assump_37
        case intro assump_42 assump_43 =>
          apply False.elim assump_43
      case inr assump_39 =>
        cases assump_37
        case intro assump_50 assump_51 =>
          apply False.elim assump_51


variable (p7 p6 p0 p3 : Prop)
theorem file64_98977 : (((((p0 ∨ False) → (True ∨ True)) ∨ ((p3 ∧ p0) → (p6 ∨ p7))) → False) → False) := by
  intro assump_5
  have assump_19 : (((p0 ∨ False) → (True ∨ True)) ∨ ((p3 ∧ p0) → (p6 ∨ p7))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply Or.inl
      apply True.intro
    case inr assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p5 p4 p6 p3 p1 p2 : Prop)
theorem file64_99470 : ((((((p2 → True) → (False → p1)) ∧ ((p6 → p4) → (p4 → False))) ∧ (((False ∧ p5) ∧ (p5 → False)) ∧ ((p4 → p3) → False))) ∧ ((((True ∧ p3) ∨ (True → False)) ∨ ((True → p1) → False)) → (((p5 → p2) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16


variable (p5 p6 p1 p3 p0 p7 : Prop)
theorem file64_100191 : (((((p5 → p5) → (True → False)) → ((p3 ∨ p1) ∨ (p6 ∧ p0))) → (((p7 → p7) ∨ (p6 ∧ False)) → False)) → False) := by
  intro assump_1
  have assump_23 : (((p5 → p5) → (True → False)) → ((p3 ∨ p1) ∨ (p6 ∧ p0))) := by
    intro assump_5
    have assump_24 : (p5 → p5) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_24
    have assump_25 : True := by
      apply True.intro
    let assump_12 := assump_8 assump_25
    apply False.elim assump_12
  let assump_4 := assump_1 assump_23
  have assump_26 : ((p7 → p7) ∨ (p6 ∧ False)) := by
    apply Or.inl
    intro assump_17
    exact assump_17
  let assump_16 := assump_4 assump_26
  apply False.elim assump_16


variable (p7 p4 p3 p0 p5 p2 : Prop)
theorem file64_100940 : (((((p4 ∨ p4) → False) ∧ ((False → False) → (p0 → p5))) ∧ (((p5 ∨ True) ∨ (p2 → False)) → False)) → ((((p4 ∨ p3) ∨ (True → True)) ∧ ((p7 → p0) → False)) → (((p0 ∧ p2) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_1
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            have assump_66 : ((p5 ∨ True) ∨ (p2 → False)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_26 := assump_17 assump_66
            apply False.elim assump_26
      case inr assump_11 =>
        cases assump_1
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            have assump_67 : ((p5 ∨ True) ∨ (p2 → False)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_44 := assump_35 assump_67
            apply False.elim assump_44
    case inr assump_9 =>
      cases assump_1
      case intro assump_52 assump_53 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          have assump_68 : ((p5 ∨ True) ∨ (p2 → False)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_62 := assump_53 assump_68
          apply False.elim assump_62


variable (p3 p5 p6 p4 p0 p1 : Prop)
theorem file64_102537 : ((((((p1 → False) → (p5 → p6)) ∧ ((True → p6) ∨ (p0 → p5))) ∧ (((p6 → False) → False) → ((p4 → False) ∨ (p4 → p0)))) ∧ ((((True → False) → False) → False) ∧ (((True → False) → False) → ((p3 ∨ p4) → (p4 → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            have assump_72 : ((True → False) → False) := by
              intro assump_32
              have assump_73 : True := by
                apply True.intro
              let assump_35 := assump_32 assump_73
              apply False.elim assump_35
            let assump_31 := assump_16 assump_72
            apply False.elim assump_31
        case inr assump_11 =>
          cases assump_3
          case intro assump_46 assump_47 =>
            have assump_74 : ((True → False) → False) := by
              intro assump_62
              have assump_75 : True := by
                apply True.intro
              let assump_65 := assump_62 assump_75
              apply False.elim assump_65
            let assump_61 := assump_46 assump_74
            apply False.elim assump_61


variable (p6 p2 p4 p3 p5 p1 : Prop)
theorem file64_103917 : ((((((p1 → p1) ∨ (p4 ∧ p6)) ∨ ((True → False) → False)) → (((p3 → False) → (False → True)) ∨ ((p2 → False) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p1 → p1) ∨ (p4 ∧ p6)) ∨ ((True → False) → False)) → (((p3 → False) → (False → True)) ∨ ((p2 → False) ∧ (p5 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        apply True.intro
      case inr assump_9 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          apply Or.inl
          intro assump_20
          intro assump_21
          apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_24
      intro assump_25
      apply True.intro
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p7 p4 p3 p1 p6 p5 : Prop)
theorem file64_104869 : (((((True → False) ∧ (p1 → p5)) ∧ ((p4 ∨ p2) → False)) → (((p2 → False) ∨ (p2 ∧ p2)) → ((p6 ∨ p3) ∧ (p6 ∨ p4)))) ∧ ((((p6 ∧ p6) ∧ (p1 ∨ p2)) → ((p6 → False) → False)) ∨ (((p3 → False) → False) ∨ ((p7 → p2) → False)))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_115 : True := by
          apply True.intro
        let assump_19 := assump_9 assump_115
        apply False.elim assump_19
  case inr assump_4 =>
    cases assump_4
    case intro assump_23 assump_24 =>
      cases assump_1
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          have assump_116 : (p4 ∨ p2) := by
            apply Or.inr
            exact assump_24
          let assump_39 := assump_30 assump_116
          apply False.elim assump_39
  cases assump_2
  case inl assump_43 =>
    cases assump_1
    case intro assump_47 assump_48 =>
      cases assump_47
      case intro assump_49 assump_50 =>
        have assump_117 : True := by
          apply True.intro
        let assump_59 := assump_49 assump_117
        apply False.elim assump_59
  case inr assump_44 =>
    cases assump_44
    case intro assump_63 assump_64 =>
      cases assump_1
      case intro assump_69 assump_70 =>
        cases assump_69
        case intro assump_71 assump_72 =>
          have assump_118 : (p4 ∨ p2) := by
            apply Or.inr
            exact assump_64
          let assump_79 := assump_70 assump_118
          apply False.elim assump_79
  apply Or.inl
  intro assump_83
  intro assump_84
  cases assump_83
  case intro assump_87 assump_88 =>
    cases assump_87
    case intro assump_89 assump_90 =>
      cases assump_88
      case inl assump_95 =>
        have assump_119 : p6 := by
          exact assump_90
        let assump_102 := assump_84 assump_119
        apply False.elim assump_102
      case inr assump_96 =>
        have assump_120 : p6 := by
          exact assump_90
        let assump_111 := assump_84 assump_120
        apply False.elim assump_111


variable (p4 p7 p3 p0 p6 p5 p2 : Prop)
theorem file64_107139 : ((((((p0 ∨ p7) ∨ (p2 ∧ p0)) ∧ ((False → p6) → False)) → (((p3 → p7) ∧ (p5 → p6)) → ((True ∧ False) ∨ (p6 → p4)))) → False) → False) := by
  intro assump_1
  have assump_71 : ((((p0 ∨ p7) ∨ (p2 ∧ p0)) ∧ ((False → p6) → False)) → (((p3 → p7) ∧ (p5 → p6)) → ((True ∧ False) ∨ (p6 → p4)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            apply Or.inr
            intro assump_23
            have assump_72 : (False → p6) := by
              intro assump_28
              apply False.elim assump_28
            let assump_27 := assump_14 assump_72
            apply False.elim assump_27
          case inr assump_18 =>
            apply Or.inr
            intro assump_38
            have assump_73 : (False → p6) := by
              intro assump_43
              apply False.elim assump_43
            let assump_42 := assump_14 assump_73
            apply False.elim assump_42
        case inr assump_16 =>
          cases assump_16
          case intro assump_49 assump_50 =>
            apply Or.inr
            intro assump_57
            have assump_74 : (False → p6) := by
              intro assump_62
              apply False.elim assump_62
            let assump_61 := assump_14 assump_74
            apply False.elim assump_61
  let assump_4 := assump_1 assump_71
  apply False.elim assump_4


variable (p5 p2 p7 p0 p4 p6 p3 p1 : Prop)
theorem file64_108740 : (((((True ∧ p1) → False) ∧ ((p6 ∧ p7) → False)) → (((True ∨ p4) ∨ (p3 → p5)) ∧ ((False ∧ False) → (True ∨ p2)))) ∨ ((((p7 → p0) ∧ (p1 ∧ p3)) → ((True ∧ p4) → (p7 ∨ p2))) ∨ (((p2 ∨ p1) ∨ (p4 ∨ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply False.elim assump_9


variable (p2 p0 p7 p4 p1 p3 p6 p5 : Prop)
theorem file64_109275 : (((((p5 → p2) ∨ (p5 → p5)) → ((p4 → True) → (True ∧ True))) ∨ (((True ∨ p6) ∨ (p5 ∧ p6)) → False)) ∨ ((((p2 ∨ p7) → (p5 ∨ p5)) ∧ ((p3 ∧ p0) ∨ (p0 → False))) ∧ (((p0 → p4) → (p1 → False)) → ((p2 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  apply True.intro
  apply True.intro


variable (p0 p3 p4 p7 p5 p2 p1 : Prop)
theorem file64_109679 : (((((False → p7) → (True ∧ p0)) ∧ ((True ∨ p0) ∨ (p7 ∨ p5))) → (((p5 → p0) ∧ (p2 → False)) → ((p4 ∧ p2) → False))) ∨ ((((True → False) ∧ (p3 → False)) → ((p0 ∧ p1) ∧ (p7 ∨ p7))) → (((p1 → False) ∧ (p3 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_1
      case intro assump_16 assump_17 =>
        cases assump_17
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            have assump_81 : p2 := by
              exact assump_5
            let assump_33 := assump_11 assump_81
            apply False.elim assump_33
          case inr assump_23 =>
            have assump_82 : p2 := by
              exact assump_5
            let assump_47 := assump_11 assump_82
            apply False.elim assump_47
        case inr assump_21 =>
          cases assump_21
          case inl assump_51 =>
            have assump_83 : p2 := by
              exact assump_5
            let assump_63 := assump_11 assump_83
            apply False.elim assump_63
          case inr assump_52 =>
            have assump_84 : p2 := by
              exact assump_5
            let assump_77 := assump_11 assump_84
            apply False.elim assump_77


variable (p7 p6 p4 p5 p1 p0 : Prop)
theorem file64_111086 : (((((p1 ∧ p6) ∨ (p5 → False)) ∧ ((p1 ∧ False) ∧ (p7 → False))) ∧ (((p4 ∧ p0) → (True ∨ False)) → False)) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_21
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              apply False.elim assump_33
      case inr assump_23 =>
        cases assump_21
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply False.elim assump_43


variable (p5 p3 p0 p7 p4 : Prop)
theorem file64_111897 : ((((((p3 → p4) ∧ (p7 ∨ p4)) ∧ ((True ∨ p0) → False)) → (((p5 ∨ False) ∨ (True ∨ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_96 : ((((p3 → p4) ∧ (p7 ∨ p4)) ∧ ((True ∨ p0) → False)) → (((p5 ∨ False) ∨ (True ∨ p0)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_16
            case inl assump_19 =>
              have assump_97 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_25 := assump_14 assump_97
              apply False.elim assump_25
            case inr assump_20 =>
              have assump_98 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_33 := assump_14 assump_98
              apply False.elim assump_33
      case inr assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      cases assump_8
      case inl assump_39 =>
        cases assump_5
        case intro assump_43 assump_44 =>
          cases assump_43
          case intro assump_45 assump_46 =>
            cases assump_46
            case inl assump_49 =>
              have assump_99 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_55 := assump_44 assump_99
              apply False.elim assump_55
            case inr assump_50 =>
              have assump_100 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_63 := assump_44 assump_100
              apply False.elim assump_63
      case inr assump_40 =>
        cases assump_5
        case intro assump_69 assump_70 =>
          cases assump_69
          case intro assump_71 assump_72 =>
            cases assump_72
            case inl assump_75 =>
              have assump_101 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_81 := assump_70 assump_101
              apply False.elim assump_81
            case inr assump_76 =>
              have assump_102 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_89 := assump_70 assump_102
              apply False.elim assump_89
  let assump_4 := assump_1 assump_96
  apply False.elim assump_4


variable (p0 p2 p3 p5 p4 p6 p1 : Prop)
theorem file64_114491 : (((((p2 ∨ p6) ∨ (p3 ∨ p2)) ∧ ((False → False) → False)) ∨ (((True ∧ False) → False) ∨ ((p6 ∨ p0) → False))) ∧ ((((p4 ∧ p5) ∧ (p1 ∨ p1)) ∧ ((p6 ∧ p0) ∧ (True → False))) → False)) := by
  apply And.intro
  apply Or.inr
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_12
        case inl assump_19 =>
          cases assump_10
          case intro assump_23 assump_24 =>
            cases assump_23
            case intro assump_25 assump_26 =>
              have assump_53 : True := by
                apply True.intro
              let assump_33 := assump_24 assump_53
              apply False.elim assump_33
        case inr assump_20 =>
          cases assump_10
          case intro assump_39 assump_40 =>
            cases assump_39
            case intro assump_41 assump_42 =>
              have assump_54 : True := by
                apply True.intro
              let assump_49 := assump_40 assump_54
              apply False.elim assump_49


variable (p5 p6 p4 p2 p1 p0 p3 : Prop)
theorem file64_115778 : (((((p4 ∨ p5) → (p1 ∨ p3)) → False) ∨ (((False ∧ False) → False) → ((p5 → p2) → (p1 → p4)))) → ((((p6 → False) ∧ (True → False)) → False) ∨ (((p2 ∨ p4) ∨ (p5 ∧ p5)) → ((p0 → False) ∨ (False ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_30 : True := by
        apply True.intro
      let assump_13 := assump_8 assump_30
      apply False.elim assump_13
  case inr assump_3 =>
    apply Or.inl
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      have assump_31 : True := by
        apply True.intro
      let assump_26 := assump_21 assump_31
      apply False.elim assump_26


variable (p2 p6 p1 p4 p5 : Prop)
theorem file64_116576 : (((((p5 ∧ p2) ∧ (p1 → p6)) → ((p5 → False) ∨ (True → False))) → (((p5 ∧ p4) → (p2 ∨ p5)) ∨ ((False ∧ p4) → False))) ∨ ((((p1 → False) → (p1 ∨ p1)) ∨ ((True ∨ p2) ∧ (False ∧ False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inr
    exact assump_5


variable (p7 p6 p0 p5 p4 p1 p2 : Prop)
theorem file64_116988 : (((((p5 → p6) ∨ (True → False)) → ((p6 ∧ p6) ∧ (p6 → False))) ∧ (((p6 ∧ p7) ∧ (p4 ∨ p2)) ∨ ((True → False) ∨ (p6 ∧ p7)))) → ((((p5 ∨ p1) → (p0 → False)) ∧ ((p7 ∨ p0) ∧ (p2 → p4))) → (((p0 ∨ p0) ∨ (False → p6)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_1
            case intro assump_22 assump_23 =>
              cases assump_23
              case inl assump_26 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_29
                    case inl assump_36 =>
                      have assump_530 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_44
                        exact assump_30
                      let assump_43 := assump_22 assump_530
                      let assump_47 := And.right assump_43
                      have assump_531 : p6 := by
                        exact assump_30
                      let assump_51 := assump_47 assump_531
                      apply False.elim assump_51
                    case inr assump_37 =>
                      have assump_532 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_61
                        exact assump_30
                      let assump_60 := assump_22 assump_532
                      let assump_64 := And.right assump_60
                      have assump_533 : p6 := by
                        exact assump_30
                      let assump_68 := assump_64 assump_533
                      apply False.elim assump_68
              case inr assump_27 =>
                cases assump_27
                case inl assump_72 =>
                  have assump_534 : True := by
                    apply True.intro
                  let assump_76 := assump_72 assump_534
                  apply False.elim assump_76
                case inr assump_73 =>
                  cases assump_73
                  case intro assump_80 assump_81 =>
                    have assump_535 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_89
                      exact assump_80
                    let assump_88 := assump_22 assump_535
                    let assump_92 := And.right assump_88
                    have assump_536 : p6 := by
                      exact assump_80
                    let assump_96 := assump_92 assump_536
                    apply False.elim assump_96
          case inr assump_17 =>
            cases assump_1
            case intro assump_104 assump_105 =>
              cases assump_105
              case inl assump_108 =>
                cases assump_108
                case intro assump_110 assump_111 =>
                  cases assump_110
                  case intro assump_112 assump_113 =>
                    cases assump_111
                    case inl assump_118 =>
                      have assump_537 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_126
                        exact assump_112
                      let assump_125 := assump_104 assump_537
                      let assump_129 := And.right assump_125
                      have assump_538 : p6 := by
                        exact assump_112
                      let assump_133 := assump_129 assump_538
                      apply False.elim assump_133
                    case inr assump_119 =>
                      have assump_539 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_143
                        exact assump_112
                      let assump_142 := assump_104 assump_539
                      let assump_146 := And.right assump_142
                      have assump_540 : p6 := by
                        exact assump_112
                      let assump_150 := assump_146 assump_540
                      apply False.elim assump_150
              case inr assump_109 =>
                cases assump_109
                case inl assump_154 =>
                  have assump_541 : True := by
                    apply True.intro
                  let assump_158 := assump_154 assump_541
                  apply False.elim assump_158
                case inr assump_155 =>
                  cases assump_155
                  case intro assump_162 assump_163 =>
                    have assump_542 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_171
                      exact assump_162
                    let assump_170 := assump_104 assump_542
                    let assump_174 := And.right assump_170
                    have assump_543 : p6 := by
                      exact assump_162
                    let assump_178 := assump_174 assump_543
                    apply False.elim assump_178
    case inr assump_7 =>
      cases assump_2
      case intro assump_184 assump_185 =>
        cases assump_185
        case intro assump_188 assump_189 =>
          cases assump_188
          case inl assump_190 =>
            cases assump_1
            case intro assump_196 assump_197 =>
              cases assump_197
              case inl assump_200 =>
                cases assump_200
                case intro assump_202 assump_203 =>
                  cases assump_202
                  case intro assump_204 assump_205 =>
                    cases assump_203
                    case inl assump_210 =>
                      have assump_544 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_218
                        exact assump_204
                      let assump_217 := assump_196 assump_544
                      let assump_221 := And.right assump_217
                      have assump_545 : p6 := by
                        exact assump_204
                      let assump_225 := assump_221 assump_545
                      apply False.elim assump_225
                    case inr assump_211 =>
                      have assump_546 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_235
                        exact assump_204
                      let assump_234 := assump_196 assump_546
                      let assump_238 := And.right assump_234
                      have assump_547 : p6 := by
                        exact assump_204
                      let assump_242 := assump_238 assump_547
                      apply False.elim assump_242
              case inr assump_201 =>
                cases assump_201
                case inl assump_246 =>
                  have assump_548 : True := by
                    apply True.intro
                  let assump_250 := assump_246 assump_548
                  apply False.elim assump_250
                case inr assump_247 =>
                  cases assump_247
                  case intro assump_254 assump_255 =>
                    have assump_549 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_263
                      exact assump_254
                    let assump_262 := assump_196 assump_549
                    let assump_266 := And.right assump_262
                    have assump_550 : p6 := by
                      exact assump_254
                    let assump_270 := assump_266 assump_550
                    apply False.elim assump_270
          case inr assump_191 =>
            cases assump_1
            case intro assump_278 assump_279 =>
              cases assump_279
              case inl assump_282 =>
                cases assump_282
                case intro assump_284 assump_285 =>
                  cases assump_284
                  case intro assump_286 assump_287 =>
                    cases assump_285
                    case inl assump_292 =>
                      have assump_551 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_300
                        exact assump_286
                      let assump_299 := assump_278 assump_551
                      let assump_303 := And.right assump_299
                      have assump_552 : p6 := by
                        exact assump_286
                      let assump_307 := assump_303 assump_552
                      apply False.elim assump_307
                    case inr assump_293 =>
                      have assump_553 : ((p5 → p6) ∨ (True → False)) := by
                        apply Or.inl
                        intro assump_317
                        exact assump_286
                      let assump_316 := assump_278 assump_553
                      let assump_320 := And.right assump_316
                      have assump_554 : p6 := by
                        exact assump_286
                      let assump_324 := assump_320 assump_554
                      apply False.elim assump_324
              case inr assump_283 =>
                cases assump_283
                case inl assump_328 =>
                  have assump_555 : True := by
                    apply True.intro
                  let assump_332 := assump_328 assump_555
                  apply False.elim assump_332
                case inr assump_329 =>
                  cases assump_329
                  case intro assump_336 assump_337 =>
                    have assump_556 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_345
                      exact assump_336
                    let assump_344 := assump_278 assump_556
                    let assump_348 := And.right assump_344
                    have assump_557 : p6 := by
                      exact assump_336
                    let assump_352 := assump_348 assump_557
                    apply False.elim assump_352
  case inr assump_5 =>
    cases assump_2
    case intro assump_358 assump_359 =>
      cases assump_359
      case intro assump_362 assump_363 =>
        cases assump_362
        case inl assump_364 =>
          cases assump_1
          case intro assump_370 assump_371 =>
            cases assump_371
            case inl assump_374 =>
              cases assump_374
              case intro assump_376 assump_377 =>
                cases assump_376
                case intro assump_378 assump_379 =>
                  cases assump_377
                  case inl assump_384 =>
                    have assump_558 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_392
                      exact assump_378
                    let assump_391 := assump_370 assump_558
                    let assump_395 := And.right assump_391
                    have assump_559 : p6 := by
                      exact assump_378
                    let assump_399 := assump_395 assump_559
                    apply False.elim assump_399
                  case inr assump_385 =>
                    have assump_560 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_409
                      exact assump_378
                    let assump_408 := assump_370 assump_560
                    let assump_412 := And.right assump_408
                    have assump_561 : p6 := by
                      exact assump_378
                    let assump_416 := assump_412 assump_561
                    apply False.elim assump_416
            case inr assump_375 =>
              cases assump_375
              case inl assump_420 =>
                have assump_562 : True := by
                  apply True.intro
                let assump_424 := assump_420 assump_562
                apply False.elim assump_424
              case inr assump_421 =>
                cases assump_421
                case intro assump_428 assump_429 =>
                  have assump_563 : ((p5 → p6) ∨ (True → False)) := by
                    apply Or.inl
                    intro assump_437
                    exact assump_428
                  let assump_436 := assump_370 assump_563
                  let assump_440 := And.right assump_436
                  have assump_564 : p6 := by
                    exact assump_428
                  let assump_444 := assump_440 assump_564
                  apply False.elim assump_444
        case inr assump_365 =>
          cases assump_1
          case intro assump_452 assump_453 =>
            cases assump_453
            case inl assump_456 =>
              cases assump_456
              case intro assump_458 assump_459 =>
                cases assump_458
                case intro assump_460 assump_461 =>
                  cases assump_459
                  case inl assump_466 =>
                    have assump_565 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_474
                      exact assump_460
                    let assump_473 := assump_452 assump_565
                    let assump_477 := And.right assump_473
                    have assump_566 : p6 := by
                      exact assump_460
                    let assump_481 := assump_477 assump_566
                    apply False.elim assump_481
                  case inr assump_467 =>
                    have assump_567 : ((p5 → p6) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_491
                      exact assump_460
                    let assump_490 := assump_452 assump_567
                    let assump_494 := And.right assump_490
                    have assump_568 : p6 := by
                      exact assump_460
                    let assump_498 := assump_494 assump_568
                    apply False.elim assump_498
            case inr assump_457 =>
              cases assump_457
              case inl assump_502 =>
                have assump_569 : True := by
                  apply True.intro
                let assump_506 := assump_502 assump_569
                apply False.elim assump_506
              case inr assump_503 =>
                cases assump_503
                case intro assump_510 assump_511 =>
                  have assump_570 : ((p5 → p6) ∨ (True → False)) := by
                    apply Or.inl
                    intro assump_519
                    exact assump_510
                  let assump_518 := assump_452 assump_570
                  let assump_522 := And.right assump_518
                  have assump_571 : p6 := by
                    exact assump_510
                  let assump_526 := assump_522 assump_571
                  apply False.elim assump_526


variable (p7 p3 p1 p5 p4 p2 : Prop)
theorem file64_132266 : ((((((p3 ∨ p1) → False) → ((p5 → p1) ∨ (p7 ∨ p2))) → (((p4 ∨ p1) ∧ (p5 → p4)) ∨ ((p5 → False) ∨ (p5 → False)))) ∧ ((((False → p4) → False) → ((True → p5) → (p1 → p7))) → (((p5 ∧ False) → False) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_40 : (((False → p4) → False) → ((True → p5) → (p1 → p7))) := by
      intro assump_13
      intro assump_14
      intro assump_15
      have assump_41 : (False → p4) := by
        intro assump_23
        apply False.elim assump_23
      let assump_22 := assump_13 assump_41
      apply False.elim assump_22
    let assump_12 := assump_7 assump_40
    have assump_42 : ((p5 ∧ False) → False) := by
      intro assump_30
      cases assump_30
      case intro assump_31 assump_32 =>
        apply False.elim assump_32
    let assump_29 := assump_12 assump_42
    apply False.elim assump_29


variable (p1 p7 p4 p6 p3 p0 p2 : Prop)
theorem file64_133221 : (((((True → False) ∧ (p0 → p3)) → False) ∨ (((p4 ∧ p3) → (p7 ∨ p1)) → ((p6 ∧ p1) → False))) → ((((p3 ∨ p0) ∧ (p2 ∧ False)) ∧ ((p0 ∨ p2) ∨ (p0 ∨ False))) → False)) := by
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_12
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      case inr assump_14 =>
        cases assump_12
        case intro assump_25 assump_26 =>
          apply False.elim assump_26


variable (p0 p6 p7 p4 p1 : Prop)
theorem file64_133874 : ((((((p6 → False) ∧ (p7 → False)) ∧ ((p4 ∨ p6) ∨ (False ∧ True))) → (((p1 → p0) ∧ (p1 ∧ False)) → False)) → False) → False) := by
  intro assump_11
  have assump_30 : ((((p6 → False) ∧ (p7 → False)) ∧ ((p4 ∨ p6) ∨ (False ∧ True))) → (((p1 → p0) ∧ (p1 ∧ False)) → False)) := by
    intro assump_15
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        apply False.elim assump_22
  let assump_14 := assump_11 assump_30
  apply False.elim assump_14


variable (p3 p5 p0 p6 p2 p4 : Prop)
theorem file64_134474 : ((((((p6 → p6) ∨ (p0 ∨ p6)) ∨ ((p2 → p3) → (True → False))) ∨ (((p4 → False) ∨ (p6 → False)) → ((p3 → p6) → (p6 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 → p6) ∨ (p0 ∨ p6)) ∨ ((p2 → p3) → (True → False))) ∨ (((p4 → False) ∨ (p6 → False)) → ((p3 → p6) → (p6 ∧ p5)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p6 p1 p4 p3 p5 p0 : Prop)
theorem file64_134997 : ((((((True → False) → (p4 ∨ p5)) ∨ ((p0 → False) → False)) → False) ∧ ((((p0 → False) ∧ (p3 → False)) ∨ ((p3 ∧ False) ∧ (p1 ∧ p7))) ∧ (((p1 → False) ∧ (p0 → False)) ∧ ((p6 ∨ True) ∧ (p3 ∨ p7))))) → False) := by
  intro assump_51
  cases assump_51
  case intro assump_52 assump_53 =>
    cases assump_53
    case intro assump_56 assump_57 =>
      cases assump_56
      case inl assump_58 =>
        cases assump_58
        case intro assump_60 assump_61 =>
          cases assump_57
          case intro assump_66 assump_67 =>
            cases assump_66
            case intro assump_68 assump_69 =>
              cases assump_67
              case intro assump_74 assump_75 =>
                cases assump_74
                case inl assump_76 =>
                  cases assump_75
                  case inl assump_80 =>
                    have assump_150 : p3 := by
                      exact assump_80
                    let assump_88 := assump_61 assump_150
                    apply False.elim assump_88
                  case inr assump_81 =>
                    have assump_151 : (((True → False) → (p4 ∨ p5)) ∨ ((p0 → False) → False)) := by
                      apply Or.inl
                      intro assump_101
                      have assump_152 : True := by
                        apply True.intro
                      let assump_104 := assump_101 assump_152
                      apply False.elim assump_104
                    let assump_100 := assump_52 assump_151
                    apply False.elim assump_100
                case inr assump_77 =>
                  cases assump_75
                  case inl assump_113 =>
                    have assump_153 : p3 := by
                      exact assump_113
                    let assump_120 := assump_61 assump_153
                    apply False.elim assump_120
                  case inr assump_114 =>
                    have assump_154 : (((True → False) → (p4 ∨ p5)) ∨ ((p0 → False) → False)) := by
                      apply Or.inl
                      intro assump_132
                      have assump_155 : True := by
                        apply True.intro
                      let assump_135 := assump_132 assump_155
                      apply False.elim assump_135
                    let assump_131 := assump_52 assump_154
                    apply False.elim assump_131
      case inr assump_59 =>
        cases assump_59
        case intro assump_142 assump_143 =>
          cases assump_142
          case intro assump_144 assump_145 =>
            apply False.elim assump_145


variable (p4 p7 : Prop)
theorem file64_137624 : (((((True → False) ∧ (p4 ∧ p7)) → False) → False) → False) := by
  intro assump_1
  have assump_25 : (((True → False) ∧ (p4 ∧ p7)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p5 p0 p6 p3 p2 p1 p7 : Prop)
theorem file64_138175 : ((((((p2 ∧ p6) → (p7 → False)) → False) → (((p3 ∨ p3) ∨ (p3 → p0)) → ((p1 → p1) ∨ (p2 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p2 ∧ p6) → (p7 → False)) → False) → (((p3 ∨ p3) ∨ (p3 → p0)) → ((p1 → p1) ∨ (p2 ∨ p5)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_15
        exact assump_15
      case inr assump_10 =>
        apply Or.inl
        intro assump_22
        exact assump_22
    case inr assump_8 =>
      apply Or.inl
      intro assump_29
      exact assump_29
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p4 p0 p3 p2 p6 p7 : Prop)
theorem file64_138938 : ((((((p0 ∨ p2) ∧ (p6 ∧ p0)) → False) ∨ (((p2 → p7) ∧ (p4 → False)) → False)) ∧ ((((p7 → p4) ∧ (p4 → p3)) → ((True → False) → (p0 ∨ p0))) → False)) → False) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      have assump_61 : (((p7 → p4) ∧ (p4 → p3)) → ((True → False) → (p0 ∨ p0))) := by
        intro assump_18
        intro assump_19
        cases assump_18
        case intro assump_22 assump_23 =>
          have assump_62 : True := by
            apply True.intro
          let assump_30 := assump_19 assump_62
          apply False.elim assump_30
      let assump_17 := assump_10 assump_61
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_63 : (((p7 → p4) ∧ (p4 → p3)) → ((True → False) → (p0 ∨ p0))) := by
        intro assump_42
        intro assump_43
        cases assump_42
        case intro assump_46 assump_47 =>
          have assump_64 : True := by
            apply True.intro
          let assump_54 := assump_43 assump_64
          apply False.elim assump_54
      let assump_41 := assump_10 assump_63
      apply False.elim assump_41


variable (p3 p4 p1 : Prop)
theorem file64_140145 : ((((((False ∨ p1) ∧ (p3 ∧ p1)) ∧ ((p1 → False) ∧ (p4 → p3))) → False) → False) → False) := by
  intro assump_1
  have assump_36 : ((((False ∨ p1) ∧ (p3 ∧ p1)) ∧ ((p1 → False) ∧ (p4 → p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              have assump_37 : p1 := by
                exact assump_17
              let assump_29 := assump_22 assump_37
              apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p1 p3 p7 p5 p0 p2 p4 p6 : Prop)
theorem file64_141039 : ((((((p4 ∧ p4) ∧ (True ∨ p6)) ∨ ((p7 ∨ p1) ∧ (False → False))) ∧ (((p3 ∨ p1) ∨ (p5 ∨ p4)) → ((p0 ∨ p2) ∧ (p2 → True)))) ∧ ((((p4 ∨ p0) ∨ (p2 → True)) ∨ ((p3 → p1) ∨ (p4 → p7))) → (((p3 → True) ∨ (p5 ∧ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_9
            case inl assump_16 =>
              have assump_76 : (((p4 ∨ p0) ∨ (p2 → True)) ∨ ((p3 → p1) ∨ (p4 → p7))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_11
              let assump_24 := assump_3 assump_76
              have assump_77 : ((p3 → True) ∨ (p5 ∧ p0)) := by
                apply Or.inl
                intro assump_26
                apply True.intro
              let assump_25 := assump_24 assump_77
              apply False.elim assump_25
            case inr assump_17 =>
              have assump_78 : (((p4 ∨ p0) ∨ (p2 → True)) ∨ ((p3 → p1) ∨ (p4 → p7))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_11
              let assump_36 := assump_3 assump_78
              have assump_79 : ((p3 → True) ∨ (p5 ∧ p0)) := by
                apply Or.inl
                intro assump_38
                apply True.intro
              let assump_37 := assump_36 assump_79
              apply False.elim assump_37
      case inr assump_7 =>
        cases assump_7
        case intro assump_42 assump_43 =>
          cases assump_42
          case inl assump_44 =>
            have assump_80 : (((p4 ∨ p0) ∨ (p2 → True)) ∨ ((p3 → p1) ∨ (p4 → p7))) := by
              apply Or.inl
              apply Or.inr
              intro assump_55
              apply True.intro
            let assump_54 := assump_3 assump_80
            have assump_81 : ((p3 → True) ∨ (p5 ∧ p0)) := by
              apply Or.inl
              intro assump_57
              apply True.intro
            let assump_56 := assump_54 assump_81
            apply False.elim assump_56
          case inr assump_45 =>
            have assump_82 : (((p4 ∨ p0) ∨ (p2 → True)) ∨ ((p3 → p1) ∨ (p4 → p7))) := by
              apply Or.inl
              apply Or.inr
              intro assump_70
              apply True.intro
            let assump_69 := assump_3 assump_82
            have assump_83 : ((p3 → True) ∨ (p5 ∧ p0)) := by
              apply Or.inl
              intro assump_72
              apply True.intro
            let assump_71 := assump_69 assump_83
            apply False.elim assump_71


variable (p4 p5 p0 p1 p7 p6 : Prop)
theorem file64_143907 : (((((True ∧ True) → False) → False) ∨ (((p1 → False) ∧ (False ∧ p6)) → ((p4 → False) ∧ (p4 → True)))) ∨ ((((p5 ∨ p6) → (True → False)) ∨ ((p7 → p0) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (True ∧ True) := by
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p2 p0 p1 p5 p7 p4 p6 : Prop)
theorem file64_144358 : (((((p3 → p0) ∨ (False ∧ p1)) ∨ ((p7 ∧ p1) ∨ (p7 → True))) → (((p7 → False) ∧ (p5 ∧ p1)) → False)) → ((((p1 ∨ p4) ∨ (p4 ∧ p3)) → ((p2 ∧ False) → (p0 → False))) ∨ (((p5 ∨ p6) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    apply False.elim assump_10


variable (p3 p4 p5 p7 p2 p1 p6 : Prop)
theorem file64_144787 : ((((((p2 → p4) → (p6 ∨ p5)) → ((p4 ∨ p3) ∨ (False → False))) ∨ (((p7 ∨ p1) ∧ (p4 ∨ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → p4) → (p6 ∨ p5)) → ((p4 ∨ p3) ∨ (False → False))) ∨ (((p7 ∨ p1) ∧ (p4 ∨ p2)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p1 p6 p3 p2 p0 p4 : Prop)
theorem file64_145277 : (((((p1 → False) → False) → ((p3 → False) → False)) ∧ (((p1 → p7) ∨ (p1 ∨ p3)) → False)) → ((((True ∧ p7) ∧ (p2 ∨ True)) → ((p6 → p6) ∧ (p0 → p4))) ∨ (((p0 ∨ p6) → False) → False))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inl
    intro assump_12
    apply And.intro
    intro assump_13
    cases assump_12
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_17
        case inl assump_24 =>
          exact assump_13
        case inr assump_25 =>
          exact assump_13
    intro assump_30
    cases assump_12
    case intro assump_33 assump_34 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        cases assump_34
        case inl assump_41 =>
          have assump_66 : ((p1 → p7) ∨ (p1 ∨ p3)) := by
            apply Or.inl
            intro assump_49
            exact assump_36
          let assump_48 := assump_7 assump_66
          apply False.elim assump_48
        case inr assump_42 =>
          have assump_67 : ((p1 → p7) ∨ (p1 ∨ p3)) := by
            apply Or.inl
            intro assump_60
            exact assump_36
          let assump_59 := assump_7 assump_67
          apply False.elim assump_59


variable (p2 p0 p6 p7 p4 p5 : Prop)
theorem file64_146592 : (((((p4 → True) → False) ∧ ((p2 → False) ∨ (p4 → p6))) → (((False → p7) ∧ (True → p7)) → ((p5 → False) ∨ (p4 ∨ p6)))) ∨ ((((False → p0) → False) ∧ ((p7 → False) ∨ (True → False))) → (((p4 → p7) ∨ (p2 → p5)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        apply Or.inl
        intro assump_17
        have assump_39 : (p4 → True) := by
          intro assump_23
          apply True.intro
        let assump_22 := assump_9 assump_39
        apply False.elim assump_22
      case inr assump_14 =>
        apply Or.inl
        intro assump_29
        have assump_40 : (p4 → True) := by
          intro assump_35
          apply True.intro
        let assump_34 := assump_9 assump_40
        apply False.elim assump_34


variable (p4 p5 p3 p0 p6 p2 : Prop)
theorem file64_147550 : ((((((False ∧ p0) ∨ (p3 → False)) ∧ ((False → p5) ∧ (p3 ∧ False))) → False) → ((((p2 ∨ p3) → False) ∧ ((p2 → p6) → False)) ∧ (((p4 ∨ p5) → False) → False))) → False) := by
  intro assump_1
  have assump_65 : ((((False ∧ p0) ∨ (p3 → False)) ∧ ((False → p5) ∧ (p3 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
      case inr assump_9 =>
        cases assump_7
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
  let assump_4 := assump_1 assump_65
  let assump_26 := And.left assump_4
  let assump_27 := And.right assump_26
  have assump_66 : (p2 → p6) := by
    intro assump_30
    have assump_67 : ((((False ∧ p0) ∨ (p3 → False)) ∧ ((False → p5) ∧ (p3 ∧ False))) → False) := by
      intro assump_35
      cases assump_35
      case intro assump_36 assump_37 =>
        cases assump_36
        case inl assump_38 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_40
        case inr assump_39 =>
          cases assump_37
          case intro assump_46 assump_47 =>
            cases assump_47
            case intro assump_50 assump_51 =>
              apply False.elim assump_51
    let assump_34 := assump_1 assump_67
    let assump_56 := And.left assump_34
    let assump_57 := And.left assump_56
    have assump_68 : (p2 ∨ p3) := by
      apply Or.inl
      exact assump_30
    let assump_58 := assump_57 assump_68
    apply False.elim assump_58
  let assump_29 := assump_27 assump_66
  apply False.elim assump_29


variable (p5 p4 p0 p1 p6 p7 p2 : Prop)
theorem file64_149395 : (((((p0 ∨ p2) ∧ (False ∨ p2)) → False) → (((p1 → True) → False) ∨ ((p7 ∧ p5) ∧ (p4 ∧ p0)))) → ((((p1 ∨ p6) ∧ (True ∧ False)) ∧ ((p1 ∨ p2) → False)) → (((p6 ∧ p5) ∧ (p7 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_17
            case intro assump_22 assump_23 =>
              apply False.elim assump_23
          case inr assump_19 =>
            cases assump_17
            case intro assump_30 assump_31 =>
              apply False.elim assump_31


variable (p7 p1 p4 p3 p5 p2 : Prop)
theorem file64_150254 : (((((p2 → p2) ∨ (p3 ∨ p2)) → False) → False) ∨ ((((p7 ∨ p1) ∨ (p5 → False)) ∨ ((p4 → False) → (False → False))) → False)) := by
  apply Or.inl
  intro assump_7
  have assump_17 : ((p2 → p2) ∨ (p3 ∨ p2)) := by
    apply Or.inl
    intro assump_11
    exact assump_11
  let assump_10 := assump_7 assump_17
  apply False.elim assump_10


variable (p2 p7 p4 p1 p0 p5 : Prop)
theorem file64_150647 : ((((((p7 → False) → False) → False) ∧ (((False → False) → (p2 → False)) → ((p0 ∧ p2) ∧ (True → False)))) ∧ ((((p1 ∨ p5) → False) → False) ∧ (((True → False) ∧ (p4 → True)) ∧ ((False ∨ p0) ∧ (False → p2))))) → False) := by
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
            cases assump_15
            case intro assump_22 assump_23 =>
              cases assump_22
              case inl assump_24 =>
                apply False.elim assump_24
              case inr assump_25 =>
                have assump_39 : True := by
                  apply True.intro
                let assump_35 := assump_16 assump_39
                apply False.elim assump_35


variable (p2 p5 p7 p6 p3 p0 p1 p4 : Prop)
theorem file64_151649 : (((((p4 ∨ True) → False) ∧ ((p7 ∧ p3) ∨ (True → False))) → False) ∨ ((((p4 ∧ p2) ∨ (p7 ∧ p7)) ∨ ((p6 ∧ p7) → (p3 → False))) ∨ (((p1 → p4) ∨ (p0 → False)) → ((False → p5) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_26 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_16 := assump_2 assump_26
        apply False.elim assump_16
    case inr assump_7 =>
      have assump_27 : True := by
        apply True.intro
      let assump_22 := assump_7 assump_27
      apply False.elim assump_22


variable (p3 p5 p0 p2 : Prop)
theorem file64_152408 : (((((p5 → p0) → (False → False)) ∧ ((p0 ∧ p3) → (p2 → p3))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p5 → p0) → (False → False)) ∧ ((p0 ∧ p3) → (p2 → p3))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      exact assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p5 p2 p1 p3 p0 p4 p6 : Prop)
theorem file64_152929 : ((((((p0 ∧ p2) → False) → ((p7 → p0) → (p4 → False))) ∨ (((p3 ∨ p4) ∧ (p5 ∧ p4)) → ((p2 → False) ∨ (p6 ∨ p4)))) ∧ ((((p1 ∧ p3) → False) ∧ ((p6 → True) → False)) ∧ (((p2 ∨ p2) ∨ (p6 → False)) ∨ ((p2 → p2) ∧ (p1 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                have assump_136 : (p6 → True) := by
                  intro assump_26
                  apply True.intro
                let assump_25 := assump_11 assump_136
                apply False.elim assump_25
              case inr assump_21 =>
                have assump_137 : (p6 → True) := by
                  intro assump_34
                  apply True.intro
                let assump_33 := assump_11 assump_137
                apply False.elim assump_33
            case inr assump_19 =>
              have assump_138 : (p6 → True) := by
                intro assump_42
                apply True.intro
              let assump_41 := assump_11 assump_138
              apply False.elim assump_41
          case inr assump_17 =>
            cases assump_17
            case intro assump_46 assump_47 =>
              cases assump_47
              case inl assump_50 =>
                have assump_139 : (p6 → True) := by
                  intro assump_57
                  apply True.intro
                let assump_56 := assump_11 assump_139
                apply False.elim assump_56
              case inr assump_51 =>
                have assump_140 : (p6 → True) := by
                  intro assump_67
                  apply True.intro
                let assump_66 := assump_11 assump_140
                apply False.elim assump_66
    case inr assump_5 =>
      cases assump_3
      case intro assump_73 assump_74 =>
        cases assump_73
        case intro assump_75 assump_76 =>
          cases assump_74
          case inl assump_81 =>
            cases assump_81
            case inl assump_83 =>
              cases assump_83
              case inl assump_85 =>
                have assump_141 : (p6 → True) := by
                  intro assump_91
                  apply True.intro
                let assump_90 := assump_76 assump_141
                apply False.elim assump_90
              case inr assump_86 =>
                have assump_142 : (p6 → True) := by
                  intro assump_99
                  apply True.intro
                let assump_98 := assump_76 assump_142
                apply False.elim assump_98
            case inr assump_84 =>
              have assump_143 : (p6 → True) := by
                intro assump_107
                apply True.intro
              let assump_106 := assump_76 assump_143
              apply False.elim assump_106
          case inr assump_82 =>
            cases assump_82
            case intro assump_111 assump_112 =>
              cases assump_112
              case inl assump_115 =>
                have assump_144 : (p6 → True) := by
                  intro assump_122
                  apply True.intro
                let assump_121 := assump_76 assump_144
                apply False.elim assump_121
              case inr assump_116 =>
                have assump_145 : (p6 → True) := by
                  intro assump_132
                  apply True.intro
                let assump_131 := assump_76 assump_145
                apply False.elim assump_131


variable (p5 p2 p0 p7 p3 p1 : Prop)
theorem file64_156713 : (((((p0 ∨ p5) → (p5 ∧ p7)) → ((p1 → False) → (p2 ∧ True))) ∨ (((p0 ∧ p2) → (p0 → False)) ∧ ((p7 → False) → False))) → ((((p7 → False) ∧ (p2 → p1)) → False) → (((p1 ∨ p1) → (True ∨ p3)) ∨ ((p1 → p5) ∧ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply Or.inl
      apply True.intro
    case inr assump_11 =>
      apply Or.inl
      apply True.intro
  case inr assump_6 =>
    cases assump_6
    case intro assump_16 assump_17 =>
      apply Or.inl
      intro assump_22
      cases assump_22
      case inl assump_23 =>
        apply Or.inl
        apply True.intro
      case inr assump_24 =>
        apply Or.inl
        apply True.intro


variable (p6 p5 p0 p3 p7 p1 p2 : Prop)
theorem file64_157555 : ((((((p3 ∧ False) ∨ (p2 ∨ p3)) ∨ ((True ∨ p1) ∧ (p0 → p5))) → (((p6 → True) ∧ (p7 → p3)) → ((p6 ∨ True) ∨ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p3 ∧ False) ∨ (p2 ∨ p3)) ∨ ((True ∨ p1) ∧ (p0 → p5))) → (((p6 → True) ∧ (p7 → p3)) → ((p6 ∨ True) ∨ (p1 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
        case inr assump_16 =>
          cases assump_16
          case inl assump_23 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
          case inr assump_24 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
      case inr assump_14 =>
        cases assump_14
        case intro assump_29 assump_30 =>
          cases assump_29
          case inl assump_31 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
          case inr assump_32 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


