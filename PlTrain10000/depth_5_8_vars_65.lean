variable (p5 p2 p3 p7 p1 p0 p4 p6 : Prop)
theorem file65_50 : (((((p7 ∨ True) ∧ (False → p4)) ∨ ((p6 → p3) ∨ (p0 → False))) → (((p7 ∧ p4) → (p7 → p1)) → False)) → ((((p0 ∨ p2) ∨ (p7 ∧ False)) ∧ ((p5 → p0) → (p6 ∧ p4))) ∨ (((True → True) ∨ (p1 → p3)) → ((p0 ∧ p7) ∨ (False → False))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  case inr assump_6 =>
    apply Or.inr
    intro assump_14
    apply False.elim assump_14


variable (p4 p7 p5 p0 p1 p3 p6 : Prop)
theorem file65_588 : ((((((p4 → True) ∧ (p6 → False)) → False) → (((p0 ∧ p5) ∧ (p7 ∧ False)) → ((p7 → p1) ∨ (p6 ∨ p3)))) ∧ ((((p0 ∨ p3) ∧ (p4 ∧ False)) ∧ ((p5 → False) ∧ (False ∨ p0))) ∧ (((p6 ∨ p3) → False) ∧ ((p4 → p5) ∧ (False → False))))) → False) := by
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
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
          case inr assump_13 =>
            cases assump_11
            case intro assump_24 assump_25 =>
              apply False.elim assump_25


variable (p0 p1 p3 p4 p7 p6 p2 : Prop)
theorem file65_1455 : ((((((p6 → p1) ∨ (False ∧ p6)) ∨ ((p6 → p4) ∨ (p4 → False))) ∨ (((p1 → p0) → (p2 → False)) → False)) ∧ ((((True → False) ∨ (p4 → False)) ∧ ((p3 ∧ p4) → (p7 ∧ p1))) ∧ (((p1 ∨ p4) ∧ (p0 ∨ p0)) ∧ ((True → False) ∧ (p3 ∨ p6))))) → False) := by
  intro assump_1
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
                  case intro assump_24 assump_25 =>
                    cases assump_24
                    case inl assump_26 =>
                      cases assump_25
                      case inl assump_30 =>
                        cases assump_23
                        case intro assump_34 assump_35 =>
                          cases assump_35
                          case inl assump_38 =>
                            have assump_896 : True := by
                              apply True.intro
                            let assump_43 := assump_34 assump_896
                            apply False.elim assump_43
                          case inr assump_39 =>
                            have assump_897 : True := by
                              apply True.intro
                            let assump_50 := assump_34 assump_897
                            apply False.elim assump_50
                      case inr assump_31 =>
                        cases assump_23
                        case intro assump_56 assump_57 =>
                          cases assump_57
                          case inl assump_60 =>
                            have assump_898 : True := by
                              apply True.intro
                            let assump_65 := assump_56 assump_898
                            apply False.elim assump_65
                          case inr assump_61 =>
                            have assump_899 : True := by
                              apply True.intro
                            let assump_72 := assump_56 assump_899
                            apply False.elim assump_72
                    case inr assump_27 =>
                      cases assump_25
                      case inl assump_78 =>
                        cases assump_23
                        case intro assump_82 assump_83 =>
                          cases assump_83
                          case inl assump_86 =>
                            have assump_900 : True := by
                              apply True.intro
                            let assump_91 := assump_82 assump_900
                            apply False.elim assump_91
                          case inr assump_87 =>
                            have assump_901 : True := by
                              apply True.intro
                            let assump_98 := assump_82 assump_901
                            apply False.elim assump_98
                      case inr assump_79 =>
                        cases assump_23
                        case intro assump_104 assump_105 =>
                          cases assump_105
                          case inl assump_108 =>
                            have assump_902 : True := by
                              apply True.intro
                            let assump_113 := assump_104 assump_902
                            apply False.elim assump_113
                          case inr assump_109 =>
                            have assump_903 : True := by
                              apply True.intro
                            let assump_120 := assump_104 assump_903
                            apply False.elim assump_120
              case inr assump_17 =>
                cases assump_13
                case intro assump_128 assump_129 =>
                  cases assump_128
                  case intro assump_130 assump_131 =>
                    cases assump_130
                    case inl assump_132 =>
                      cases assump_131
                      case inl assump_136 =>
                        cases assump_129
                        case intro assump_140 assump_141 =>
                          cases assump_141
                          case inl assump_144 =>
                            have assump_904 : True := by
                              apply True.intro
                            let assump_149 := assump_140 assump_904
                            apply False.elim assump_149
                          case inr assump_145 =>
                            have assump_905 : True := by
                              apply True.intro
                            let assump_156 := assump_140 assump_905
                            apply False.elim assump_156
                      case inr assump_137 =>
                        cases assump_129
                        case intro assump_162 assump_163 =>
                          cases assump_163
                          case inl assump_166 =>
                            have assump_906 : True := by
                              apply True.intro
                            let assump_171 := assump_162 assump_906
                            apply False.elim assump_171
                          case inr assump_167 =>
                            have assump_907 : True := by
                              apply True.intro
                            let assump_178 := assump_162 assump_907
                            apply False.elim assump_178
                    case inr assump_133 =>
                      cases assump_131
                      case inl assump_184 =>
                        cases assump_129
                        case intro assump_188 assump_189 =>
                          cases assump_189
                          case inl assump_192 =>
                            have assump_908 : True := by
                              apply True.intro
                            let assump_197 := assump_188 assump_908
                            apply False.elim assump_197
                          case inr assump_193 =>
                            have assump_909 : True := by
                              apply True.intro
                            let assump_204 := assump_188 assump_909
                            apply False.elim assump_204
                      case inr assump_185 =>
                        cases assump_129
                        case intro assump_210 assump_211 =>
                          cases assump_211
                          case inl assump_214 =>
                            have assump_910 : True := by
                              apply True.intro
                            let assump_219 := assump_210 assump_910
                            apply False.elim assump_219
                          case inr assump_215 =>
                            have assump_911 : True := by
                              apply True.intro
                            let assump_226 := assump_210 assump_911
                            apply False.elim assump_226
        case inr assump_9 =>
          cases assump_9
          case intro assump_230 assump_231 =>
            apply False.elim assump_230
      case inr assump_7 =>
        cases assump_7
        case inl assump_234 =>
          cases assump_3
          case intro assump_238 assump_239 =>
            cases assump_238
            case intro assump_240 assump_241 =>
              cases assump_240
              case inl assump_242 =>
                cases assump_239
                case intro assump_248 assump_249 =>
                  cases assump_248
                  case intro assump_250 assump_251 =>
                    cases assump_250
                    case inl assump_252 =>
                      cases assump_251
                      case inl assump_256 =>
                        cases assump_249
                        case intro assump_260 assump_261 =>
                          cases assump_261
                          case inl assump_264 =>
                            have assump_912 : True := by
                              apply True.intro
                            let assump_269 := assump_260 assump_912
                            apply False.elim assump_269
                          case inr assump_265 =>
                            have assump_913 : True := by
                              apply True.intro
                            let assump_276 := assump_260 assump_913
                            apply False.elim assump_276
                      case inr assump_257 =>
                        cases assump_249
                        case intro assump_282 assump_283 =>
                          cases assump_283
                          case inl assump_286 =>
                            have assump_914 : True := by
                              apply True.intro
                            let assump_291 := assump_282 assump_914
                            apply False.elim assump_291
                          case inr assump_287 =>
                            have assump_915 : True := by
                              apply True.intro
                            let assump_298 := assump_282 assump_915
                            apply False.elim assump_298
                    case inr assump_253 =>
                      cases assump_251
                      case inl assump_304 =>
                        cases assump_249
                        case intro assump_308 assump_309 =>
                          cases assump_309
                          case inl assump_312 =>
                            have assump_916 : True := by
                              apply True.intro
                            let assump_317 := assump_308 assump_916
                            apply False.elim assump_317
                          case inr assump_313 =>
                            have assump_917 : True := by
                              apply True.intro
                            let assump_324 := assump_308 assump_917
                            apply False.elim assump_324
                      case inr assump_305 =>
                        cases assump_249
                        case intro assump_330 assump_331 =>
                          cases assump_331
                          case inl assump_334 =>
                            have assump_918 : True := by
                              apply True.intro
                            let assump_339 := assump_330 assump_918
                            apply False.elim assump_339
                          case inr assump_335 =>
                            have assump_919 : True := by
                              apply True.intro
                            let assump_346 := assump_330 assump_919
                            apply False.elim assump_346
              case inr assump_243 =>
                cases assump_239
                case intro assump_354 assump_355 =>
                  cases assump_354
                  case intro assump_356 assump_357 =>
                    cases assump_356
                    case inl assump_358 =>
                      cases assump_357
                      case inl assump_362 =>
                        cases assump_355
                        case intro assump_366 assump_367 =>
                          cases assump_367
                          case inl assump_370 =>
                            have assump_920 : True := by
                              apply True.intro
                            let assump_375 := assump_366 assump_920
                            apply False.elim assump_375
                          case inr assump_371 =>
                            have assump_921 : True := by
                              apply True.intro
                            let assump_382 := assump_366 assump_921
                            apply False.elim assump_382
                      case inr assump_363 =>
                        cases assump_355
                        case intro assump_388 assump_389 =>
                          cases assump_389
                          case inl assump_392 =>
                            have assump_922 : True := by
                              apply True.intro
                            let assump_397 := assump_388 assump_922
                            apply False.elim assump_397
                          case inr assump_393 =>
                            have assump_923 : True := by
                              apply True.intro
                            let assump_404 := assump_388 assump_923
                            apply False.elim assump_404
                    case inr assump_359 =>
                      cases assump_357
                      case inl assump_410 =>
                        cases assump_355
                        case intro assump_414 assump_415 =>
                          cases assump_415
                          case inl assump_418 =>
                            have assump_924 : True := by
                              apply True.intro
                            let assump_423 := assump_414 assump_924
                            apply False.elim assump_423
                          case inr assump_419 =>
                            have assump_925 : True := by
                              apply True.intro
                            let assump_430 := assump_414 assump_925
                            apply False.elim assump_430
                      case inr assump_411 =>
                        cases assump_355
                        case intro assump_436 assump_437 =>
                          cases assump_437
                          case inl assump_440 =>
                            have assump_926 : True := by
                              apply True.intro
                            let assump_445 := assump_436 assump_926
                            apply False.elim assump_445
                          case inr assump_441 =>
                            have assump_927 : True := by
                              apply True.intro
                            let assump_452 := assump_436 assump_927
                            apply False.elim assump_452
        case inr assump_235 =>
          cases assump_3
          case intro assump_458 assump_459 =>
            cases assump_458
            case intro assump_460 assump_461 =>
              cases assump_460
              case inl assump_462 =>
                cases assump_459
                case intro assump_468 assump_469 =>
                  cases assump_468
                  case intro assump_470 assump_471 =>
                    cases assump_470
                    case inl assump_472 =>
                      cases assump_471
                      case inl assump_476 =>
                        cases assump_469
                        case intro assump_480 assump_481 =>
                          cases assump_481
                          case inl assump_484 =>
                            have assump_928 : True := by
                              apply True.intro
                            let assump_489 := assump_480 assump_928
                            apply False.elim assump_489
                          case inr assump_485 =>
                            have assump_929 : True := by
                              apply True.intro
                            let assump_496 := assump_480 assump_929
                            apply False.elim assump_496
                      case inr assump_477 =>
                        cases assump_469
                        case intro assump_502 assump_503 =>
                          cases assump_503
                          case inl assump_506 =>
                            have assump_930 : True := by
                              apply True.intro
                            let assump_511 := assump_502 assump_930
                            apply False.elim assump_511
                          case inr assump_507 =>
                            have assump_931 : True := by
                              apply True.intro
                            let assump_518 := assump_502 assump_931
                            apply False.elim assump_518
                    case inr assump_473 =>
                      cases assump_471
                      case inl assump_524 =>
                        cases assump_469
                        case intro assump_528 assump_529 =>
                          cases assump_529
                          case inl assump_532 =>
                            have assump_932 : True := by
                              apply True.intro
                            let assump_537 := assump_528 assump_932
                            apply False.elim assump_537
                          case inr assump_533 =>
                            have assump_933 : True := by
                              apply True.intro
                            let assump_544 := assump_528 assump_933
                            apply False.elim assump_544
                      case inr assump_525 =>
                        cases assump_469
                        case intro assump_550 assump_551 =>
                          cases assump_551
                          case inl assump_554 =>
                            have assump_934 : True := by
                              apply True.intro
                            let assump_559 := assump_550 assump_934
                            apply False.elim assump_559
                          case inr assump_555 =>
                            have assump_935 : True := by
                              apply True.intro
                            let assump_566 := assump_550 assump_935
                            apply False.elim assump_566
              case inr assump_463 =>
                cases assump_459
                case intro assump_574 assump_575 =>
                  cases assump_574
                  case intro assump_576 assump_577 =>
                    cases assump_576
                    case inl assump_578 =>
                      cases assump_577
                      case inl assump_582 =>
                        cases assump_575
                        case intro assump_586 assump_587 =>
                          cases assump_587
                          case inl assump_590 =>
                            have assump_936 : True := by
                              apply True.intro
                            let assump_595 := assump_586 assump_936
                            apply False.elim assump_595
                          case inr assump_591 =>
                            have assump_937 : True := by
                              apply True.intro
                            let assump_602 := assump_586 assump_937
                            apply False.elim assump_602
                      case inr assump_583 =>
                        cases assump_575
                        case intro assump_608 assump_609 =>
                          cases assump_609
                          case inl assump_612 =>
                            have assump_938 : True := by
                              apply True.intro
                            let assump_617 := assump_608 assump_938
                            apply False.elim assump_617
                          case inr assump_613 =>
                            have assump_939 : True := by
                              apply True.intro
                            let assump_624 := assump_608 assump_939
                            apply False.elim assump_624
                    case inr assump_579 =>
                      cases assump_577
                      case inl assump_630 =>
                        cases assump_575
                        case intro assump_634 assump_635 =>
                          cases assump_635
                          case inl assump_638 =>
                            have assump_940 : True := by
                              apply True.intro
                            let assump_643 := assump_634 assump_940
                            apply False.elim assump_643
                          case inr assump_639 =>
                            have assump_941 : True := by
                              apply True.intro
                            let assump_650 := assump_634 assump_941
                            apply False.elim assump_650
                      case inr assump_631 =>
                        cases assump_575
                        case intro assump_656 assump_657 =>
                          cases assump_657
                          case inl assump_660 =>
                            have assump_942 : True := by
                              apply True.intro
                            let assump_665 := assump_656 assump_942
                            apply False.elim assump_665
                          case inr assump_661 =>
                            have assump_943 : True := by
                              apply True.intro
                            let assump_672 := assump_656 assump_943
                            apply False.elim assump_672
    case inr assump_5 =>
      cases assump_3
      case intro assump_678 assump_679 =>
        cases assump_678
        case intro assump_680 assump_681 =>
          cases assump_680
          case inl assump_682 =>
            cases assump_679
            case intro assump_688 assump_689 =>
              cases assump_688
              case intro assump_690 assump_691 =>
                cases assump_690
                case inl assump_692 =>
                  cases assump_691
                  case inl assump_696 =>
                    cases assump_689
                    case intro assump_700 assump_701 =>
                      cases assump_701
                      case inl assump_704 =>
                        have assump_944 : True := by
                          apply True.intro
                        let assump_709 := assump_700 assump_944
                        apply False.elim assump_709
                      case inr assump_705 =>
                        have assump_945 : True := by
                          apply True.intro
                        let assump_716 := assump_700 assump_945
                        apply False.elim assump_716
                  case inr assump_697 =>
                    cases assump_689
                    case intro assump_722 assump_723 =>
                      cases assump_723
                      case inl assump_726 =>
                        have assump_946 : True := by
                          apply True.intro
                        let assump_731 := assump_722 assump_946
                        apply False.elim assump_731
                      case inr assump_727 =>
                        have assump_947 : True := by
                          apply True.intro
                        let assump_738 := assump_722 assump_947
                        apply False.elim assump_738
                case inr assump_693 =>
                  cases assump_691
                  case inl assump_744 =>
                    cases assump_689
                    case intro assump_748 assump_749 =>
                      cases assump_749
                      case inl assump_752 =>
                        have assump_948 : True := by
                          apply True.intro
                        let assump_757 := assump_748 assump_948
                        apply False.elim assump_757
                      case inr assump_753 =>
                        have assump_949 : True := by
                          apply True.intro
                        let assump_764 := assump_748 assump_949
                        apply False.elim assump_764
                  case inr assump_745 =>
                    cases assump_689
                    case intro assump_770 assump_771 =>
                      cases assump_771
                      case inl assump_774 =>
                        have assump_950 : True := by
                          apply True.intro
                        let assump_779 := assump_770 assump_950
                        apply False.elim assump_779
                      case inr assump_775 =>
                        have assump_951 : True := by
                          apply True.intro
                        let assump_786 := assump_770 assump_951
                        apply False.elim assump_786
          case inr assump_683 =>
            cases assump_679
            case intro assump_794 assump_795 =>
              cases assump_794
              case intro assump_796 assump_797 =>
                cases assump_796
                case inl assump_798 =>
                  cases assump_797
                  case inl assump_802 =>
                    cases assump_795
                    case intro assump_806 assump_807 =>
                      cases assump_807
                      case inl assump_810 =>
                        have assump_952 : True := by
                          apply True.intro
                        let assump_815 := assump_806 assump_952
                        apply False.elim assump_815
                      case inr assump_811 =>
                        have assump_953 : True := by
                          apply True.intro
                        let assump_822 := assump_806 assump_953
                        apply False.elim assump_822
                  case inr assump_803 =>
                    cases assump_795
                    case intro assump_828 assump_829 =>
                      cases assump_829
                      case inl assump_832 =>
                        have assump_954 : True := by
                          apply True.intro
                        let assump_837 := assump_828 assump_954
                        apply False.elim assump_837
                      case inr assump_833 =>
                        have assump_955 : True := by
                          apply True.intro
                        let assump_844 := assump_828 assump_955
                        apply False.elim assump_844
                case inr assump_799 =>
                  cases assump_797
                  case inl assump_850 =>
                    cases assump_795
                    case intro assump_854 assump_855 =>
                      cases assump_855
                      case inl assump_858 =>
                        have assump_956 : True := by
                          apply True.intro
                        let assump_863 := assump_854 assump_956
                        apply False.elim assump_863
                      case inr assump_859 =>
                        have assump_957 : True := by
                          apply True.intro
                        let assump_870 := assump_854 assump_957
                        apply False.elim assump_870
                  case inr assump_851 =>
                    cases assump_795
                    case intro assump_876 assump_877 =>
                      cases assump_877
                      case inl assump_880 =>
                        have assump_958 : True := by
                          apply True.intro
                        let assump_885 := assump_876 assump_958
                        apply False.elim assump_885
                      case inr assump_881 =>
                        have assump_959 : True := by
                          apply True.intro
                        let assump_892 := assump_876 assump_959
                        apply False.elim assump_892


variable (p0 : Prop)
theorem file65_29408 : ((((((p0 → False) → (p0 → p0)) → False) → False) → False) → False) := by
  intro assump_7
  have assump_27 : ((((p0 → False) → (p0 → p0)) → False) → False) := by
    intro assump_11
    have assump_28 : ((p0 → False) → (p0 → p0)) := by
      intro assump_15
      intro assump_16
      exact assump_16
    let assump_14 := assump_11 assump_28
    apply False.elim assump_14
  let assump_10 := assump_7 assump_27
  apply False.elim assump_10


variable (p1 p7 p0 p6 p4 p3 : Prop)
theorem file65_29909 : (((((p7 ∧ False) → (False ∧ p7)) ∨ ((p0 → p1) → (p4 → False))) ∧ (((False → p7) ∨ (p6 → False)) → False)) → ((((p0 → p0) ∧ (p4 ∨ p7)) ∧ ((False ∨ p3) → (p6 ∧ p0))) ∧ (((p0 ∨ p4) → (p6 ∧ p6)) ∧ ((p4 ∨ True) ∧ (p6 → False))))) := by
  intro assump_26
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_27
  cases assump_26
  case intro assump_30 assump_31 =>
    cases assump_30
    case inl assump_32 =>
      exact assump_27
    case inr assump_33 =>
      exact assump_27
  cases assump_26
  case intro assump_42 assump_43 =>
    cases assump_42
    case inl assump_44 =>
      have assump_291 : ((False → p7) ∨ (p6 → False)) := by
        apply Or.inl
        intro assump_51
        apply False.elim assump_51
      let assump_50 := assump_43 assump_291
      apply False.elim assump_50
    case inr assump_45 =>
      have assump_292 : ((False → p7) ∨ (p6 → False)) := by
        apply Or.inl
        intro assump_62
        apply False.elim assump_62
      let assump_61 := assump_43 assump_292
      apply False.elim assump_61
  intro assump_68
  apply And.intro
  cases assump_68
  case inl assump_69 =>
    apply False.elim assump_69
  case inr assump_70 =>
    cases assump_26
    case intro assump_75 assump_76 =>
      cases assump_75
      case inl assump_77 =>
        have assump_293 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_84
          apply False.elim assump_84
        let assump_83 := assump_76 assump_293
        apply False.elim assump_83
      case inr assump_78 =>
        have assump_294 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_95
          apply False.elim assump_95
        let assump_94 := assump_76 assump_294
        apply False.elim assump_94
  cases assump_68
  case inl assump_101 =>
    apply False.elim assump_101
  case inr assump_102 =>
    cases assump_26
    case intro assump_107 assump_108 =>
      cases assump_107
      case inl assump_109 =>
        have assump_295 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_116
          apply False.elim assump_116
        let assump_115 := assump_108 assump_295
        apply False.elim assump_115
      case inr assump_110 =>
        have assump_296 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_127
          apply False.elim assump_127
        let assump_126 := assump_108 assump_296
        apply False.elim assump_126
  apply And.intro
  intro assump_133
  apply And.intro
  cases assump_133
  case inl assump_134 =>
    cases assump_26
    case intro assump_138 assump_139 =>
      cases assump_138
      case inl assump_140 =>
        have assump_297 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_147
          apply False.elim assump_147
        let assump_146 := assump_139 assump_297
        apply False.elim assump_146
      case inr assump_141 =>
        have assump_298 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_158
          apply False.elim assump_158
        let assump_157 := assump_139 assump_298
        apply False.elim assump_157
  case inr assump_135 =>
    cases assump_26
    case intro assump_166 assump_167 =>
      cases assump_166
      case inl assump_168 =>
        have assump_299 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_175
          apply False.elim assump_175
        let assump_174 := assump_167 assump_299
        apply False.elim assump_174
      case inr assump_169 =>
        have assump_300 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_186
          apply False.elim assump_186
        let assump_185 := assump_167 assump_300
        apply False.elim assump_185
  cases assump_133
  case inl assump_192 =>
    cases assump_26
    case intro assump_196 assump_197 =>
      cases assump_196
      case inl assump_198 =>
        have assump_301 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_205
          apply False.elim assump_205
        let assump_204 := assump_197 assump_301
        apply False.elim assump_204
      case inr assump_199 =>
        have assump_302 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_216
          apply False.elim assump_216
        let assump_215 := assump_197 assump_302
        apply False.elim assump_215
  case inr assump_193 =>
    cases assump_26
    case intro assump_224 assump_225 =>
      cases assump_224
      case inl assump_226 =>
        have assump_303 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_233
          apply False.elim assump_233
        let assump_232 := assump_225 assump_303
        apply False.elim assump_232
      case inr assump_227 =>
        have assump_304 : ((False → p7) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_244
          apply False.elim assump_244
        let assump_243 := assump_225 assump_304
        apply False.elim assump_243
  apply And.intro
  cases assump_26
  case intro assump_250 assump_251 =>
    cases assump_250
    case inl assump_252 =>
      apply Or.inr
      apply True.intro
    case inr assump_253 =>
      apply Or.inr
      apply True.intro
  intro assump_262
  cases assump_26
  case intro assump_265 assump_266 =>
    cases assump_265
    case inl assump_267 =>
      have assump_305 : ((False → p7) ∨ (p6 → False)) := by
        apply Or.inl
        intro assump_274
        apply False.elim assump_274
      let assump_273 := assump_266 assump_305
      apply False.elim assump_273
    case inr assump_268 =>
      have assump_306 : ((False → p7) ∨ (p6 → False)) := by
        apply Or.inl
        intro assump_285
        apply False.elim assump_285
      let assump_284 := assump_266 assump_306
      apply False.elim assump_284


variable (p0 p1 p6 p5 p4 : Prop)
theorem file65_35909 : (((((p4 ∧ p1) ∨ (False → False)) ∨ ((p0 ∧ p6) → (p5 ∧ p0))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p4 ∧ p1) ∨ (False → False)) ∨ ((p0 ∧ p6) → (p5 ∧ p0))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p4 p2 p7 p1 p6 p3 p0 : Prop)
theorem file65_36307 : (((((p4 ∧ p1) ∧ (False → False)) → False) → (((p7 → p7) ∧ (p3 ∨ p0)) → ((p7 → True) → False))) → ((((p2 → False) ∨ (p0 ∧ p4)) ∨ ((p5 ∨ p2) → (p1 ∨ p5))) → (((p0 ∧ p2) ∨ (p3 ∧ p1)) → ((p5 → p5) ∨ (False → p6))))) := by
  intro assump_10
  intro assump_11
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_11
      case inl assump_21 =>
        cases assump_21
        case inl assump_23 =>
          apply Or.inl
          intro assump_29
          exact assump_29
        case inr assump_24 =>
          cases assump_24
          case intro assump_32 assump_33 =>
            apply Or.inl
            intro assump_40
            exact assump_40
      case inr assump_22 =>
        apply Or.inl
        intro assump_47
        exact assump_47
  case inr assump_14 =>
    cases assump_14
    case intro assump_50 assump_51 =>
      cases assump_11
      case inl assump_56 =>
        cases assump_56
        case inl assump_58 =>
          apply Or.inl
          intro assump_64
          exact assump_64
        case inr assump_59 =>
          cases assump_59
          case intro assump_67 assump_68 =>
            apply Or.inl
            intro assump_75
            exact assump_75
      case inr assump_57 =>
        apply Or.inl
        intro assump_82
        exact assump_82


variable (p2 p1 p5 p7 p3 p6 : Prop)
theorem file65_37735 : ((((((p1 → p6) → (p2 ∨ True)) ∧ ((p1 → False) ∨ (p7 ∨ p3))) ∧ (((p6 ∨ p5) ∨ (p5 → False)) → False)) ∨ ((((p7 → False) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          have assump_79 : ((p6 ∨ p5) ∨ (p5 → False)) := by
            apply Or.inr
            intro assump_17
            have assump_80 : ((p6 ∨ p5) ∨ (p5 → False)) := by
              apply Or.inl
              apply Or.inr
              exact assump_17
            let assump_21 := assump_5 assump_80
            apply False.elim assump_21
          let assump_16 := assump_5 assump_79
          apply False.elim assump_16
        case inr assump_11 =>
          cases assump_11
          case inl assump_28 =>
            have assump_81 : ((p6 ∨ p5) ∨ (p5 → False)) := by
              apply Or.inr
              intro assump_35
              have assump_82 : ((p6 ∨ p5) ∨ (p5 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_35
              let assump_39 := assump_5 assump_82
              apply False.elim assump_39
            let assump_34 := assump_5 assump_81
            apply False.elim assump_34
          case inr assump_29 =>
            have assump_83 : ((p6 ∨ p5) ∨ (p5 → False)) := by
              apply Or.inr
              intro assump_51
              have assump_84 : ((p6 ∨ p5) ∨ (p5 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_51
              let assump_55 := assump_5 assump_84
              apply False.elim assump_55
            let assump_50 := assump_5 assump_83
            apply False.elim assump_50
  case inr assump_3 =>
    have assump_85 : (((p7 → False) ∧ (True → False)) → False) := by
      intro assump_65
      cases assump_65
      case intro assump_66 assump_67 =>
        have assump_86 : True := by
          apply True.intro
        let assump_72 := assump_67 assump_86
        apply False.elim assump_72
    let assump_64 := assump_3 assump_85
    apply False.elim assump_64


variable (p6 p2 p3 p4 p0 p5 : Prop)
theorem file65_40030 : ((((((p2 → False) ∧ (p6 ∨ p5)) → False) ∨ (((False ∧ False) → (p0 ∨ False)) → ((p0 → False) ∧ (p4 ∧ p3)))) ∧ ((((False → p5) ∨ (p0 → p3)) ∨ ((p2 ∧ p3) → (p4 ∧ p6))) → False)) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case inl assump_22 =>
      have assump_46 : (((False → p5) ∨ (p0 → p3)) ∨ ((p2 ∧ p3) → (p4 ∧ p6))) := by
        apply Or.inl
        apply Or.inl
        intro assump_29
        apply False.elim assump_29
      let assump_28 := assump_21 assump_46
      apply False.elim assump_28
    case inr assump_23 =>
      have assump_47 : (((False → p5) ∨ (p0 → p3)) ∨ ((p2 ∧ p3) → (p4 ∧ p6))) := by
        apply Or.inl
        apply Or.inl
        intro assump_40
        apply False.elim assump_40
      let assump_39 := assump_21 assump_47
      apply False.elim assump_39


variable (p1 p0 p2 p7 : Prop)
theorem file65_40940 : (((((False → False) ∨ (False → False)) → False) ∧ (((p1 ∨ True) ∧ (p2 ∨ p7)) ∧ ((False → p2) ∧ (p7 → False)))) → ((((p1 ∧ p2) → False) → ((p1 → False) → (p0 ∨ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            cases assump_10
            case intro assump_21 assump_22 =>
              have assump_84 : ((False → False) ∨ (False → False)) := by
                apply Or.inl
                intro assump_32
                apply False.elim assump_32
              let assump_31 := assump_5 assump_84
              apply False.elim assump_31
          case inr assump_18 =>
            cases assump_10
            case intro assump_40 assump_41 =>
              have assump_85 : p7 := by
                exact assump_18
              let assump_46 := assump_41 assump_85
              apply False.elim assump_46
        case inr assump_14 =>
          cases assump_12
          case inl assump_52 =>
            cases assump_10
            case intro assump_56 assump_57 =>
              have assump_86 : ((False → False) ∨ (False → False)) := by
                apply Or.inl
                intro assump_66
                apply False.elim assump_66
              let assump_65 := assump_5 assump_86
              apply False.elim assump_65
          case inr assump_53 =>
            cases assump_10
            case intro assump_74 assump_75 =>
              have assump_87 : p7 := by
                exact assump_53
              let assump_80 := assump_75 assump_87
              apply False.elim assump_80


variable (p6 p1 p2 p7 p0 p4 p5 p3 : Prop)
theorem file65_42815 : ((((((p1 ∧ p6) → (p3 ∨ p7)) → ((p4 ∨ p5) → (True ∨ p5))) ∨ (((p4 → p4) ∧ (p5 → False)) → ((p2 → False) → False))) ∧ ((((p4 ∨ p2) ∨ (p2 → p3)) ∧ ((p3 ∨ p0) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_54 : (((p4 ∨ p2) ∨ (p2 → p3)) ∧ ((p3 ∨ p0) → (False → False))) := by
        apply And.intro
        apply Or.inr
        intro assump_11
        have assump_55 : (((p4 ∨ p2) ∨ (p2 → p3)) ∧ ((p3 ∨ p0) → (False → False))) := by
          apply And.intro
          apply Or.inl
          apply Or.inr
          exact assump_11
          intro assump_16
          intro assump_17
          apply False.elim assump_17
        let assump_15 := assump_3 assump_55
        apply False.elim assump_15
        intro assump_23
        intro assump_24
        apply False.elim assump_24
      let assump_10 := assump_3 assump_54
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_56 : (((p4 ∨ p2) ∨ (p2 → p3)) ∧ ((p3 ∨ p0) → (False → False))) := by
        apply And.intro
        apply Or.inr
        intro assump_35
        have assump_57 : (((p4 ∨ p2) ∨ (p2 → p3)) ∧ ((p3 ∨ p0) → (False → False))) := by
          apply And.intro
          apply Or.inl
          apply Or.inr
          exact assump_35
          intro assump_40
          intro assump_41
          apply False.elim assump_41
        let assump_39 := assump_3 assump_57
        apply False.elim assump_39
        intro assump_47
        intro assump_48
        apply False.elim assump_48
      let assump_34 := assump_3 assump_56
      apply False.elim assump_34


variable (p0 p3 p5 p4 p7 : Prop)
theorem file65_44547 : (((((p0 → False) → (p3 ∧ p4)) ∧ ((p3 → p7) ∧ (True → p7))) ∧ (((False → False) ∨ (p5 ∧ p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_23 : ((False → False) ∨ (p5 ∧ p0)) := by
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p4 p7 p5 p1 p2 p0 p6 p3 : Prop)
theorem file65_45138 : (((((p6 ∧ p1) → False) ∧ ((p1 ∧ False) ∧ (p1 ∧ p7))) ∧ (((p1 → False) ∨ (p6 ∧ p2)) ∨ ((p0 → p3) → (p2 ∨ p3)))) → ((((p7 ∧ p3) → False) → False) → (((p1 ∧ p3) ∨ (p3 → False)) ∨ ((p5 ∧ p7) → (p2 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_14


variable (p2 p4 p6 p7 p5 p3 p1 : Prop)
theorem file65_45714 : (((((p6 ∨ p7) → False) → ((False ∧ p5) → (p2 ∨ p3))) → False) → ((((p1 → False) → (p6 → True)) → ((p7 ∧ False) → (p4 → False))) ∨ (((p7 → p6) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    apply False.elim assump_10


variable (p3 p7 p2 p4 p5 p0 : Prop)
theorem file65_46108 : (((((True → False) → False) ∨ ((True → False) → (False ∨ p7))) → (((p7 ∨ p0) → (False → False)) ∨ ((p5 ∨ p3) ∧ (p0 ∨ p3)))) ∨ ((((True ∨ p4) ∧ (p4 ∧ p4)) ∨ ((False → False) ∧ (p2 → p5))) ∨ (((True ∨ False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    apply Or.inl
    intro assump_12
    intro assump_13
    apply False.elim assump_13


variable (p7 p3 p5 p6 p0 p1 p4 : Prop)
theorem file65_46671 : (((((p6 → False) ∨ (p3 ∧ p0)) → False) ∧ (((True ∨ p4) → False) ∨ ((p7 ∧ p7) → (False → False)))) → ((((p7 → p3) → False) → False) → (((p1 ∧ False) → (p6 ∧ p5)) ∨ ((p0 → p4) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      apply Or.inl
      intro assump_13
      apply And.intro
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
      cases assump_13
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
    case inr assump_10 =>
      apply Or.inl
      intro assump_28
      apply And.intro
      cases assump_28
      case intro assump_29 assump_30 =>
        apply False.elim assump_30
      cases assump_28
      case intro assump_35 assump_36 =>
        apply False.elim assump_36


variable (p0 p5 p2 p4 p6 p1 p7 p3 : Prop)
theorem file65_47607 : (((((False ∨ p5) → (True ∧ p1)) ∧ ((p0 ∧ p3) ∧ (p2 ∨ p1))) ∨ (((False → False) ∧ (p3 → False)) ∨ ((True ∧ p3) ∧ (p3 ∧ p3)))) → ((((p7 ∨ p3) ∨ (p0 ∨ p0)) → ((p6 ∧ p1) ∨ (p3 ∨ True))) ∨ (((p4 ∨ p3) → False) ∧ ((p5 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            apply Or.inl
            intro assump_20
            cases assump_20
            case inl assump_21 =>
              cases assump_21
              case inl assump_23 =>
                apply Or.inr
                apply Or.inl
                exact assump_11
              case inr assump_24 =>
                apply Or.inr
                apply Or.inl
                exact assump_24
            case inr assump_22 =>
              cases assump_22
              case inl assump_29 =>
                apply Or.inr
                apply Or.inl
                exact assump_11
              case inr assump_30 =>
                apply Or.inr
                apply Or.inl
                exact assump_11
          case inr assump_17 =>
            apply Or.inl
            intro assump_37
            cases assump_37
            case inl assump_38 =>
              cases assump_38
              case inl assump_40 =>
                apply Or.inr
                apply Or.inl
                exact assump_11
              case inr assump_41 =>
                apply Or.inr
                apply Or.inl
                exact assump_41
            case inr assump_39 =>
              cases assump_39
              case inl assump_46 =>
                apply Or.inr
                apply Or.inl
                exact assump_11
              case inr assump_47 =>
                apply Or.inr
                apply Or.inl
                exact assump_11
  case inr assump_3 =>
    cases assump_3
    case inl assump_52 =>
      cases assump_52
      case intro assump_54 assump_55 =>
        apply Or.inl
        intro assump_60
        cases assump_60
        case inl assump_61 =>
          cases assump_61
          case inl assump_63 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
          case inr assump_64 =>
            apply Or.inr
            apply Or.inl
            exact assump_64
        case inr assump_62 =>
          cases assump_62
          case inl assump_69 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
          case inr assump_70 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
    case inr assump_53 =>
      cases assump_53
      case intro assump_75 assump_76 =>
        cases assump_75
        case intro assump_77 assump_78 =>
          cases assump_76
          case intro assump_83 assump_84 =>
            apply Or.inl
            intro assump_89
            cases assump_89
            case inl assump_90 =>
              cases assump_90
              case inl assump_92 =>
                apply Or.inr
                apply Or.inl
                exact assump_84
              case inr assump_93 =>
                apply Or.inr
                apply Or.inl
                exact assump_93
            case inr assump_91 =>
              cases assump_91
              case inl assump_98 =>
                apply Or.inr
                apply Or.inl
                exact assump_84
              case inr assump_99 =>
                apply Or.inr
                apply Or.inl
                exact assump_84


variable (p4 p3 p0 p6 p5 p7 : Prop)
theorem file65_51348 : (((((False → False) → False) → ((p4 ∧ p7) ∨ (True ∧ p4))) → False) → ((((p7 → p6) ∧ (p5 → False)) → False) ∧ (((p0 → False) → False) → ((p0 ∨ p3) ∨ (p6 ∧ p5))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_44 : (((False → False) → False) → ((p4 ∧ p7) ∨ (True ∧ p4))) := by
      intro assump_12
      have assump_45 : (False → False) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_12 assump_45
      apply False.elim assump_15
    let assump_11 := assump_1 assump_44
    apply False.elim assump_11
  intro assump_25
  have assump_46 : (((False → False) → False) → ((p4 ∧ p7) ∨ (True ∧ p4))) := by
    intro assump_31
    have assump_47 : (False → False) := by
      intro assump_35
      apply False.elim assump_35
    let assump_34 := assump_31 assump_47
    apply False.elim assump_34
  let assump_30 := assump_1 assump_46
  apply False.elim assump_30


variable (p4 p1 p5 p0 p7 : Prop)
theorem file65_52388 : ((((((p7 → False) → False) → ((p4 → True) ∨ (p5 ∧ p1))) → (((True ∨ p4) ∨ (p5 → p1)) ∨ ((p4 → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p7 → False) → False) → ((p4 → True) ∨ (p5 ∧ p1))) → (((True ∨ p4) ∨ (p5 → p1)) ∨ ((p4 → p0) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p7 p5 p0 p6 p2 p1 : Prop)
theorem file65_52889 : (((((p5 → False) ∧ (p5 ∨ p1)) ∧ ((p7 ∨ p1) → (p1 → False))) → (((p6 → p0) → (True → False)) → False)) ∨ ((((p2 ∨ p7) → False) → ((p1 → False) ∨ (p7 → p3))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        have assump_32 : p5 := by
          exact assump_11
        let assump_19 := assump_7 assump_32
        apply False.elim assump_19
      case inr assump_12 =>
        have assump_33 : (p7 ∨ p1) := by
          apply Or.inr
          exact assump_12
        let assump_27 := assump_6 assump_33
        have assump_34 : p1 := by
          exact assump_12
        let assump_28 := assump_27 assump_34
        apply False.elim assump_28


variable (p7 p3 p2 p6 : Prop)
theorem file65_53760 : (((((p3 → p6) → False) ∧ ((False → False) → False)) ∧ (((p2 ∨ p7) ∧ (p6 ∧ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_20 : (False → False) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_5 assump_20
      apply False.elim assump_13


variable (p2 p5 p0 p6 p3 : Prop)
theorem file65_54223 : ((((((True ∧ False) ∧ (p6 → False)) → ((p2 ∧ p3) ∨ (p0 ∨ p5))) → False) ∧ ((((False → False) → False) → False) → False)) → False) := by
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


variable (p6 p3 p5 : Prop)
theorem file65_54810 : (((((p6 ∨ p3) ∧ (p5 → False)) ∨ ((False → False) ∨ (p6 ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p6 ∨ p3) ∧ (p5 → False)) ∨ ((False → False) ∨ (p6 ∧ p3))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p7 p2 p4 p1 p3 : Prop)
theorem file65_55208 : (((((p3 → p1) → (p7 ∨ p4)) → False) → False) → ((((p4 → p1) → False) → ((p2 ∨ p1) → (p3 → p5))) → (((p3 ∧ p7) ∨ (p2 ∨ p1)) → ((p7 ∨ p5) → (p3 → p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_3
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        exact assump_14
    case inr assump_13 =>
      cases assump_13
      case inl assump_24 =>
        exact assump_5
      case inr assump_25 =>
        exact assump_5
  case inr assump_9 =>
    cases assump_3
    case inl assump_40 =>
      cases assump_40
      case intro assump_42 assump_43 =>
        exact assump_42
    case inr assump_41 =>
      cases assump_41
      case inl assump_52 =>
        exact assump_5
      case inr assump_53 =>
        exact assump_5


variable (p5 p4 p0 p7 p2 p6 : Prop)
theorem file65_56136 : (((((p2 → False) ∧ (p5 → False)) → ((p7 → p0) → (False → p6))) ∨ (((p4 → p2) ∧ (p4 ∨ True)) → False)) ∨ ((((p2 ∧ p7) → False) ∧ ((True ∨ p2) → False)) ∧ (((p2 ∧ p4) ∨ (p2 → False)) → ((True ∧ p4) ∧ (p4 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p2 p0 p3 p4 p1 p5 : Prop)
theorem file65_56526 : (((((False ∧ p0) ∧ (p4 → p2)) → ((p1 ∧ p3) → False)) ∨ (((p2 ∧ p3) ∧ (p5 → False)) → ((p4 → False) ∨ (p2 ∧ True)))) ∨ ((((False ∧ True) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11


variable (p7 p3 : Prop)
theorem file65_57011 : ((((((False → False) → False) ∧ ((p7 ∧ p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → False) → False) ∧ ((p7 ∧ p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_24 : (False → False) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_6 assump_24
      apply False.elim assump_13
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p3 p2 p1 p0 p6 : Prop)
theorem file65_57577 : ((((((p1 → True) → False) ∧ ((p3 ∨ p2) → (p3 → False))) → (((p0 → False) → (p6 → p5)) ∧ ((p2 → False) → (p5 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_56 : ((((p1 → True) → False) ∧ ((p3 ∨ p2) → (p3 → False))) → (((p0 → False) → (p6 → p5)) ∧ ((p2 → False) → (p5 ∧ p5)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      have assump_57 : (p1 → True) := by
        intro assump_20
        apply True.intro
      let assump_19 := assump_12 assump_57
      apply False.elim assump_19
    intro assump_24
    apply And.intro
    cases assump_5
    case intro assump_27 assump_28 =>
      have assump_58 : (p1 → True) := by
        intro assump_35
        apply True.intro
      let assump_34 := assump_27 assump_58
      apply False.elim assump_34
    cases assump_5
    case intro assump_41 assump_42 =>
      have assump_59 : (p1 → True) := by
        intro assump_49
        apply True.intro
      let assump_48 := assump_41 assump_59
      apply False.elim assump_48
  let assump_4 := assump_1 assump_56
  apply False.elim assump_4


variable (p5 p1 p0 p4 p2 p3 : Prop)
theorem file65_58786 : ((((((p0 → False) → (p3 ∨ False)) ∨ ((p1 → p5) ∨ (p1 → False))) → False) ∧ ((((p5 ∧ False) ∨ (True → False)) ∨ ((p4 ∧ p2) → False)) ∧ (((p2 → False) ∨ (p4 → p2)) ∧ ((p1 ∧ p4) ∧ (p1 → False))))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
        case inr assump_19 =>
          cases assump_15
          case intro assump_28 assump_29 =>
            cases assump_28
            case inl assump_30 =>
              cases assump_29
              case intro assump_34 assump_35 =>
                cases assump_34
                case intro assump_36 assump_37 =>
                  have assump_102 : p1 := by
                    exact assump_36
                  let assump_44 := assump_35 assump_102
                  apply False.elim assump_44
            case inr assump_31 =>
              cases assump_29
              case intro assump_50 assump_51 =>
                cases assump_50
                case intro assump_52 assump_53 =>
                  have assump_103 : p1 := by
                    exact assump_52
                  let assump_60 := assump_51 assump_103
                  apply False.elim assump_60
      case inr assump_17 =>
        cases assump_15
        case intro assump_66 assump_67 =>
          cases assump_66
          case inl assump_68 =>
            cases assump_67
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                have assump_104 : p1 := by
                  exact assump_74
                let assump_82 := assump_73 assump_104
                apply False.elim assump_82
          case inr assump_69 =>
            cases assump_67
            case intro assump_88 assump_89 =>
              cases assump_88
              case intro assump_90 assump_91 =>
                have assump_105 : p1 := by
                  exact assump_90
                let assump_98 := assump_89 assump_105
                apply False.elim assump_98


variable (p7 p6 p4 p1 p2 p0 p3 : Prop)
theorem file65_61115 : (((((p3 ∨ p6) → False) ∧ ((p2 ∨ p1) → False)) → (((p6 ∧ p3) ∧ (p1 → False)) ∨ ((p7 → False) → (p7 → False)))) → ((((p3 → p0) ∧ (p2 → p7)) ∧ ((p4 ∨ p7) ∧ (False ∧ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
        case inr assump_14 =>
          cases assump_12
          case intro assump_23 assump_24 =>
            apply False.elim assump_23


variable (p6 p5 p0 p1 p2 p4 : Prop)
theorem file65_61862 : ((((((p2 → p6) ∨ (p2 → p1)) ∧ ((p6 → p1) ∨ (p5 ∧ p5))) → (((True ∧ p0) ∧ (p0 → p4)) → ((p5 → False) → (p1 → p0)))) → False) → False) := by
  intro assump_1
  have assump_54 : ((((p2 → p6) ∨ (p2 → p1)) ∧ ((p6 → p1) ∨ (p5 ∧ p5))) → (((True ∧ p0) ∧ (p0 → p4)) → ((p5 → False) → (p1 → p0)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_5
        case intro assump_23 assump_24 =>
          cases assump_23
          case inl assump_25 =>
            cases assump_24
            case inl assump_29 =>
              exact assump_16
            case inr assump_30 =>
              cases assump_30
              case intro assump_33 assump_34 =>
                exact assump_16
          case inr assump_26 =>
            cases assump_24
            case inl assump_41 =>
              exact assump_16
            case inr assump_42 =>
              cases assump_42
              case intro assump_45 assump_46 =>
                exact assump_16
  let assump_4 := assump_1 assump_54
  apply False.elim assump_4


variable (p1 p7 p4 : Prop)
theorem file65_63094 : (((((False → False) ∧ (p1 ∧ p7)) → ((p4 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((False → False) ∧ (p1 ∧ p7)) → ((p4 ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p3 p6 p2 p4 : Prop)
theorem file65_63523 : ((((((p7 → False) → (p3 ∨ False)) ∨ ((p6 ∨ p7) → False)) ∧ (((p2 → False) → False) → ((True ∧ p6) → False))) ∧ ((((True → False) ∧ (p3 ∨ p7)) → ((p3 → False) ∧ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_122 : (((True → False) ∧ (p3 ∨ p7)) → ((p3 → False) ∧ (p4 → False))) := by
          intro assump_15
          apply And.intro
          intro assump_16
          cases assump_15
          case intro assump_19 assump_20 =>
            cases assump_20
            case inl assump_23 =>
              have assump_123 : True := by
                apply True.intro
              let assump_28 := assump_19 assump_123
              apply False.elim assump_28
            case inr assump_24 =>
              have assump_124 : True := by
                apply True.intro
              let assump_35 := assump_19 assump_124
              apply False.elim assump_35
          intro assump_39
          cases assump_15
          case intro assump_42 assump_43 =>
            cases assump_43
            case inl assump_46 =>
              have assump_125 : True := by
                apply True.intro
              let assump_51 := assump_42 assump_125
              apply False.elim assump_51
            case inr assump_47 =>
              have assump_126 : True := by
                apply True.intro
              let assump_58 := assump_42 assump_126
              apply False.elim assump_58
        let assump_14 := assump_3 assump_122
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_127 : (((True → False) ∧ (p3 ∨ p7)) → ((p3 → False) ∧ (p4 → False))) := by
          intro assump_72
          apply And.intro
          intro assump_73
          cases assump_72
          case intro assump_76 assump_77 =>
            cases assump_77
            case inl assump_80 =>
              have assump_128 : True := by
                apply True.intro
              let assump_85 := assump_76 assump_128
              apply False.elim assump_85
            case inr assump_81 =>
              have assump_129 : True := by
                apply True.intro
              let assump_92 := assump_76 assump_129
              apply False.elim assump_92
          intro assump_96
          cases assump_72
          case intro assump_99 assump_100 =>
            cases assump_100
            case inl assump_103 =>
              have assump_130 : True := by
                apply True.intro
              let assump_108 := assump_99 assump_130
              apply False.elim assump_108
            case inr assump_104 =>
              have assump_131 : True := by
                apply True.intro
              let assump_115 := assump_99 assump_131
              apply False.elim assump_115
        let assump_71 := assump_3 assump_127
        apply False.elim assump_71


variable (p3 p7 p6 p0 p5 p1 p2 : Prop)
theorem file65_66566 : ((((((p0 ∧ p0) → False) ∧ ((p7 ∨ p7) ∧ (p7 ∨ p5))) → False) ∧ ((((p2 → p2) → False) ∧ ((p7 ∨ p7) → False)) ∧ (((p6 → False) ∧ (True → p1)) ∨ ((p3 ∧ p5) → False)))) → False) := by
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
            have assump_44 : (p2 → p2) := by
              intro assump_27
              exact assump_27
            let assump_26 := assump_8 assump_44
            apply False.elim assump_26
        case inr assump_15 =>
          have assump_45 : (p2 → p2) := by
            intro assump_38
            exact assump_38
          let assump_37 := assump_8 assump_45
          apply False.elim assump_37


variable (p2 p0 p1 p7 : Prop)
theorem file65_67508 : ((((((p0 ∨ p2) ∧ (p2 ∧ False)) ∧ ((p0 ∧ p7) ∨ (p1 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p0 ∨ p2) ∧ (p2 ∧ False)) ∧ ((p0 ∧ p7) ∨ (p1 ∧ False))) → False) := by
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


variable (p4 p0 p2 p5 p3 p1 : Prop)
theorem file65_68269 : (((((p5 → True) → (p5 → p1)) → False) ∧ (((p2 ∨ p4) ∧ (p0 ∧ False)) ∨ ((p4 ∨ p5) → False))) → ((((False ∨ p5) ∧ (True → False)) ∧ ((False ∨ False) ∨ (p3 ∧ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        apply False.elim assump_7
      case inr assump_8 =>
        cases assump_4
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            apply False.elim assump_17
          case inr assump_18 =>
            apply False.elim assump_18
        case inr assump_16 =>
          cases assump_16
          case intro assump_23 assump_24 =>
            cases assump_1
            case intro assump_29 assump_30 =>
              cases assump_30
              case inl assump_33 =>
                cases assump_33
                case intro assump_35 assump_36 =>
                  cases assump_35
                  case inl assump_37 =>
                    cases assump_36
                    case intro assump_41 assump_42 =>
                      apply False.elim assump_42
                  case inr assump_38 =>
                    cases assump_36
                    case intro assump_49 assump_50 =>
                      apply False.elim assump_50
              case inr assump_34 =>
                have assump_61 : (p4 ∨ p5) := by
                  apply Or.inr
                  exact assump_8
                let assump_57 := assump_34 assump_61
                apply False.elim assump_57


variable (p3 p6 p5 p7 p1 p4 p0 : Prop)
theorem file65_69939 : (((((p5 ∨ False) ∧ (p4 ∨ p0)) → False) → (((p0 ∨ p7) → (p0 → True)) ∧ ((True → False) → False))) ∨ ((((p5 ∧ p7) → (p0 ∨ p4)) → False) ∧ (((True → False) ∨ (p1 → False)) → ((p6 ∨ p3) ∧ (p3 → False))))) := by
  apply Or.inl
  intro assump_5
  apply And.intro
  intro assump_6
  intro assump_7
  apply True.intro
  intro assump_8
  have assump_18 : True := by
    apply True.intro
  let assump_14 := assump_8 assump_18
  apply False.elim assump_14


variable (p0 p1 p4 p6 p2 p5 p3 : Prop)
theorem file65_70447 : (((((p4 → False) → False) → ((p1 ∧ p5) → (False → p4))) ∧ (((p1 ∧ False) ∧ (p5 ∧ p4)) → False)) → ((((p0 → False) ∧ (p3 ∧ True)) → False) → (((False → False) ∨ (p6 → False)) ∧ ((p4 → p2) → (True ∨ p5))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  intro assump_14
  cases assump_1
  case intro assump_19 assump_20 =>
    apply Or.inl
    apply True.intro


variable (p6 p5 p4 p0 p1 p2 p3 p7 : Prop)
theorem file65_71004 : (((((p2 ∨ p4) ∧ (p5 → p4)) ∧ ((p2 ∧ p7) ∧ (p3 → False))) ∧ (((False → p3) → False) → ((p7 → False) → (p7 ∧ False)))) → ((((False → True) ∨ (False ∨ p1)) ∧ ((p2 ∧ p7) → (p2 ∧ p4))) → (((p0 ∨ True) → (p6 → False)) → ((False ∨ p6) ∨ (p7 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_17
              case intro assump_26 assump_27 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  apply Or.inr
                  apply Or.inl
                  exact assump_29
            case inr assump_21 =>
              cases assump_17
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  apply Or.inr
                  apply Or.inl
                  exact assump_45
    case inr assump_9 =>
      cases assump_9
      case inl assump_54 =>
        apply False.elim assump_54
      case inr assump_55 =>
        cases assump_1
        case intro assump_62 assump_63 =>
          cases assump_62
          case intro assump_64 assump_65 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              cases assump_66
              case inl assump_68 =>
                cases assump_65
                case intro assump_74 assump_75 =>
                  cases assump_74
                  case intro assump_76 assump_77 =>
                    apply Or.inr
                    apply Or.inl
                    exact assump_77
              case inr assump_69 =>
                cases assump_65
                case intro assump_90 assump_91 =>
                  cases assump_90
                  case intro assump_92 assump_93 =>
                    apply Or.inr
                    apply Or.inl
                    exact assump_93


variable (p2 p4 p7 p3 : Prop)
theorem file65_73247 : (((((True → False) → (p2 ∨ p2)) ∨ ((p7 ∨ p4) → (p2 → p3))) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → (p2 ∨ p2)) ∨ ((p7 ∨ p4) → (p2 → p3))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p4 p1 p0 p7 p5 : Prop)
theorem file65_73714 : ((((((p0 ∨ p3) ∧ (p4 → False)) ∨ ((p3 → p7) → (p7 → p7))) ∨ (((p5 ∧ p1) → False) → ((p4 ∨ False) ∧ (False ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 ∨ p3) ∧ (p4 → False)) ∨ ((p3 → p7) → (p7 → p7))) ∨ (((p5 ∧ p1) → False) → ((p4 ∨ False) ∧ (False ∧ p5)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p4 p1 p2 p7 p6 p3 p0 : Prop)
theorem file65_74227 : ((((((p6 ∧ True) ∧ (p4 ∧ p6)) → ((True → p0) ∧ (p0 ∨ p6))) ∧ (((p0 ∧ False) → False) → False)) ∧ ((((p0 ∨ p7) ∧ (p6 → p1)) → False) ∧ (((p3 → p0) ∨ (p0 → p7)) ∨ ((True → p2) ∨ (p1 → False))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          cases assump_18
          case inl assump_20 =>
            have assump_85 : ((p0 ∧ False) → False) := by
              intro assump_27
              cases assump_27
              case intro assump_28 assump_29 =>
                apply False.elim assump_29
            let assump_26 := assump_9 assump_85
            apply False.elim assump_26
          case inr assump_21 =>
            have assump_86 : ((p0 ∧ False) → False) := by
              intro assump_42
              cases assump_42
              case intro assump_43 assump_44 =>
                apply False.elim assump_44
            let assump_41 := assump_9 assump_86
            apply False.elim assump_41
        case inr assump_19 =>
          cases assump_19
          case inl assump_52 =>
            have assump_87 : ((p0 ∧ False) → False) := by
              intro assump_60
              cases assump_60
              case intro assump_61 assump_62 =>
                apply False.elim assump_62
            let assump_59 := assump_9 assump_87
            apply False.elim assump_59
          case inr assump_53 =>
            have assump_88 : ((p0 ∧ False) → False) := by
              intro assump_75
              cases assump_75
              case intro assump_76 assump_77 =>
                apply False.elim assump_77
            let assump_74 := assump_9 assump_88
            apply False.elim assump_74


variable (p1 p7 p5 : Prop)
theorem file65_76118 : (((((p1 → False) → False) → ((p7 ∧ False) ∧ (p5 → False))) ∧ (((p5 ∧ False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p5 ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p0 p3 p1 p2 p5 p4 p7 : Prop)
theorem file65_76595 : (((((p7 → True) ∧ (p2 ∨ p5)) ∧ ((p7 ∧ False) → (p7 ∨ p7))) → (((p0 ∧ False) ∧ (p4 → False)) → ((False → p1) ∨ (False ∧ p4)))) → ((((True → False) ∧ (p5 → False)) → False) ∨ (((False → False) ∧ (p3 ∨ False)) → ((p3 ∧ p1) ∨ (p3 ∧ p4))))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    have assump_20 : True := by
      apply True.intro
    let assump_16 := assump_9 assump_20
    apply False.elim assump_16


variable (p3 p0 p7 p4 p1 p5 p2 : Prop)
theorem file65_77127 : (((((p0 ∨ p3) → (p2 → False)) → ((p2 → False) → False)) ∧ (((p1 → p4) ∧ (p2 → False)) ∧ ((p7 ∧ p4) → (p5 ∧ p4)))) → ((((True → False) → (p7 → False)) → False) → (((p0 ∨ p1) → (p7 → p4)) ∨ ((p7 → p0) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inl
        intro assump_19
        intro assump_20
        cases assump_19
        case inl assump_23 =>
          have assump_84 : ((p0 ∨ p3) → (p2 → False)) := by
            intro assump_33
            intro assump_34
            cases assump_33
            case inl assump_37 =>
              have assump_85 : p2 := by
                exact assump_34
              let assump_46 := assump_12 assump_85
              apply False.elim assump_46
            case inr assump_38 =>
              have assump_86 : p2 := by
                exact assump_34
              let assump_57 := assump_12 assump_86
              apply False.elim assump_57
          let assump_32 := assump_5 assump_84
          have assump_87 : (p2 → False) := by
            intro assump_62
            have assump_88 : p2 := by
              exact assump_62
            let assump_69 := assump_12 assump_88
            apply False.elim assump_69
          let assump_61 := assump_32 assump_87
          apply False.elim assump_61
        case inr assump_24 =>
          have assump_89 : p1 := by
            exact assump_24
          let assump_82 := assump_11 assump_89
          exact assump_82


variable (p4 p0 p3 p2 p7 : Prop)
theorem file65_78802 : (((((p0 ∨ p3) ∨ (True ∨ p4)) → False) ∨ (((p0 → p2) ∨ (p2 → p7)) ∧ ((p0 ∨ p7) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_58 : ((p0 ∨ p3) ∨ (True ∨ p4)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_6 := assump_2 assump_58
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            have assump_59 : True := by
              apply True.intro
            let assump_24 := assump_17 assump_59
            apply False.elim assump_24
          case inr assump_19 =>
            have assump_60 : True := by
              apply True.intro
            let assump_32 := assump_17 assump_60
            apply False.elim assump_32
      case inr assump_13 =>
        cases assump_11
        case intro assump_38 assump_39 =>
          cases assump_38
          case inl assump_40 =>
            have assump_61 : True := by
              apply True.intro
            let assump_46 := assump_39 assump_61
            apply False.elim assump_46
          case inr assump_41 =>
            have assump_62 : True := by
              apply True.intro
            let assump_54 := assump_39 assump_62
            apply False.elim assump_54


variable (p0 p4 p6 p7 p2 p5 p1 : Prop)
theorem file65_80324 : (((((p2 ∧ p2) ∧ (p0 ∧ p0)) → ((False ∧ p6) → False)) ∨ (((p1 → p4) → False) → ((True → False) → False))) ∨ ((((p4 → p0) ∨ (p6 ∨ p4)) ∨ ((p5 → False) ∧ (p6 → p7))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p6 p2 p7 p4 p3 p0 p5 : Prop)
theorem file65_80711 : (((((False ∧ p5) ∧ (p7 → False)) ∧ ((p5 ∧ True) → (p5 → p7))) ∨ (((True ∧ p6) ∨ (p3 ∨ p4)) → ((False ∧ p5) → (True ∨ False)))) → ((((p7 ∧ False) ∧ (p7 → False)) ∨ ((p2 → False) ∧ (p3 → False))) → (((p0 ∧ p5) ∨ (p4 ∧ p3)) → ((p3 ∧ True) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case inl assump_11 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_2
        case inl assump_19 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              apply False.elim assump_24
        case inr assump_20 =>
          cases assump_20
          case intro assump_29 assump_30 =>
            cases assump_1
            case inl assump_35 =>
              cases assump_35
              case intro assump_37 assump_38 =>
                cases assump_37
                case intro assump_39 assump_40 =>
                  cases assump_39
                  case intro assump_41 assump_42 =>
                    apply False.elim assump_41
            case inr assump_36 =>
              have assump_93 : p3 := by
                exact assump_5
              let assump_49 := assump_30 assump_93
              apply False.elim assump_49
    case inr assump_12 =>
      cases assump_12
      case intro assump_53 assump_54 =>
        cases assump_2
        case inl assump_59 =>
          cases assump_59
          case intro assump_61 assump_62 =>
            cases assump_61
            case intro assump_63 assump_64 =>
              apply False.elim assump_64
        case inr assump_60 =>
          cases assump_60
          case intro assump_69 assump_70 =>
            cases assump_1
            case inl assump_75 =>
              cases assump_75
              case intro assump_77 assump_78 =>
                cases assump_77
                case intro assump_79 assump_80 =>
                  cases assump_79
                  case intro assump_81 assump_82 =>
                    apply False.elim assump_81
            case inr assump_76 =>
              have assump_94 : p3 := by
                exact assump_54
              let assump_89 := assump_70 assump_94
              apply False.elim assump_89


variable (p1 p0 p6 p2 p4 p3 p5 : Prop)
theorem file65_83121 : (((((p0 → True) → (p6 ∨ p1)) ∨ ((True → False) ∧ (False → False))) ∧ (((p1 ∧ p2) ∧ (p2 → False)) ∧ ((True → p5) ∨ (p5 ∨ p1)))) → ((((p4 → False) → False) ∧ ((True → False) → False)) → (((p2 → False) → False) ∨ ((p6 → False) → (p3 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_16
              case inl assump_27 =>
                apply Or.inl
                intro assump_31
                have assump_107 : p2 := by
                  exact assump_20
                let assump_34 := assump_31 assump_107
                apply False.elim assump_34
              case inr assump_28 =>
                cases assump_28
                case inl assump_38 =>
                  apply Or.inl
                  intro assump_42
                  have assump_108 : p2 := by
                    exact assump_20
                  let assump_45 := assump_42 assump_108
                  apply False.elim assump_45
                case inr assump_39 =>
                  apply Or.inl
                  intro assump_51
                  have assump_109 : p2 := by
                    exact assump_20
                  let assump_54 := assump_51 assump_109
                  apply False.elim assump_54
      case inr assump_12 =>
        cases assump_12
        case intro assump_58 assump_59 =>
          cases assump_10
          case intro assump_64 assump_65 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                cases assump_65
                case inl assump_76 =>
                  apply Or.inl
                  intro assump_80
                  have assump_110 : p2 := by
                    exact assump_69
                  let assump_83 := assump_80 assump_110
                  apply False.elim assump_83
                case inr assump_77 =>
                  cases assump_77
                  case inl assump_87 =>
                    apply Or.inl
                    intro assump_91
                    have assump_111 : p2 := by
                      exact assump_69
                    let assump_94 := assump_91 assump_111
                    apply False.elim assump_94
                  case inr assump_88 =>
                    apply Or.inl
                    intro assump_100
                    have assump_112 : p2 := by
                      exact assump_69
                    let assump_103 := assump_100 assump_112
                    apply False.elim assump_103


variable (p1 p2 p6 p7 : Prop)
theorem file65_86070 : ((((((p1 ∧ p2) ∧ (p1 → p6)) → False) → (((True ∨ p7) → False) → ((True → False) → (p7 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p1 ∧ p2) ∧ (p1 → p6)) → False) → (((True ∨ p7) → False) → ((True → False) → (p7 ∧ False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    have assump_34 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_15 := assump_6 assump_34
    apply False.elim assump_15
    have assump_35 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_26 := assump_6 assump_35
    apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p3 p1 p0 p5 p6 p7 p4 : Prop)
theorem file65_86839 : (((((True ∨ p0) → False) ∧ ((p6 ∧ p3) → False)) → False) ∨ ((((p1 → p3) → (p0 → False)) → ((p3 ∧ p5) → False)) ∧ (((p1 → True) → False) → ((p4 ∧ p6) ∨ (p5 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (True ∨ p0) := by
      apply Or.inl
      apply True.intro
    let assump_9 := assump_2 assump_13
    apply False.elim assump_9


variable (p7 p0 p3 p6 p5 p2 p4 p1 : Prop)
theorem file65_87309 : ((((((p3 ∧ True) ∧ (p7 → p0)) ∧ ((False → False) ∨ (p2 → p0))) ∧ (((p5 → False) → False) ∧ ((p1 ∨ False) ∧ (p0 ∨ p5)))) ∧ ((((p1 → p6) ∧ (p1 ∧ p4)) ∧ ((p3 → False) ∧ (p0 → False))) ∧ (((p7 ∨ p4) ∧ (p0 → p1)) → ((p2 ∧ False) → (p4 → p4))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_11
            case inl assump_22 =>
              cases assump_9
              case intro assump_26 assump_27 =>
                cases assump_27
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case inl assump_32 =>
                    cases assump_31
                    case inl assump_36 =>
                      cases assump_7
                      case intro assump_40 assump_41 =>
                        cases assump_40
                        case intro assump_42 assump_43 =>
                          cases assump_42
                          case intro assump_44 assump_45 =>
                            cases assump_45
                            case intro assump_48 assump_49 =>
                              cases assump_43
                              case intro assump_54 assump_55 =>
                                have assump_190 : p0 := by
                                  exact assump_36
                                let assump_67 := assump_55 assump_190
                                apply False.elim assump_67
                    case inr assump_37 =>
                      cases assump_7
                      case intro assump_73 assump_74 =>
                        cases assump_73
                        case intro assump_75 assump_76 =>
                          cases assump_75
                          case intro assump_77 assump_78 =>
                            cases assump_78
                            case intro assump_81 assump_82 =>
                              cases assump_76
                              case intro assump_87 assump_88 =>
                                have assump_191 : p3 := by
                                  exact assump_14
                                let assump_101 := assump_87 assump_191
                                apply False.elim assump_101
                  case inr assump_33 =>
                    apply False.elim assump_33
            case inr assump_23 =>
              cases assump_9
              case intro assump_109 assump_110 =>
                cases assump_110
                case intro assump_113 assump_114 =>
                  cases assump_113
                  case inl assump_115 =>
                    cases assump_114
                    case inl assump_119 =>
                      cases assump_7
                      case intro assump_123 assump_124 =>
                        cases assump_123
                        case intro assump_125 assump_126 =>
                          cases assump_125
                          case intro assump_127 assump_128 =>
                            cases assump_128
                            case intro assump_131 assump_132 =>
                              cases assump_126
                              case intro assump_137 assump_138 =>
                                have assump_192 : p0 := by
                                  exact assump_119
                                let assump_150 := assump_138 assump_192
                                apply False.elim assump_150
                    case inr assump_120 =>
                      cases assump_7
                      case intro assump_156 assump_157 =>
                        cases assump_156
                        case intro assump_158 assump_159 =>
                          cases assump_158
                          case intro assump_160 assump_161 =>
                            cases assump_161
                            case intro assump_164 assump_165 =>
                              cases assump_159
                              case intro assump_170 assump_171 =>
                                have assump_193 : p3 := by
                                  exact assump_14
                                let assump_184 := assump_170 assump_193
                                apply False.elim assump_184
                  case inr assump_116 =>
                    apply False.elim assump_116


variable (p5 p2 p7 p6 p0 : Prop)
theorem file65_91954 : ((((((p6 → False) ∧ (p7 → False)) → ((p6 → False) → False)) → (((p7 ∨ p5) ∧ (p0 → p0)) → ((p2 ∧ p2) ∨ (False → p6)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p6 → False) ∧ (p7 → False)) → ((p6 → False) → False)) → (((p7 ∨ p5) ∧ (p0 → p0)) → ((p2 ∧ p2) ∨ (False → p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inr
        intro assump_17
        apply False.elim assump_17
      case inr assump_10 =>
        apply Or.inr
        intro assump_26
        apply False.elim assump_26
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p5 p1 p0 p4 : Prop)
theorem file65_92702 : ((((((p5 ∧ True) ∨ (True ∨ p0)) ∧ ((False → False) ∨ (p5 → False))) → (((p4 ∨ p4) → (p5 → True)) ∧ ((False → True) → (p1 → p1)))) → False) → False) := by
  intro assump_1
  have assump_51 : ((((p5 ∧ True) ∨ (True ∨ p0)) ∧ ((False → False) ∨ (p5 → False))) → (((p4 ∨ p4) → (p5 → True)) ∧ ((False → True) → (p1 → p1)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    apply True.intro
    intro assump_8
    intro assump_9
    cases assump_5
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_15
          case inl assump_24 =>
            exact assump_9
          case inr assump_25 =>
            exact assump_9
      case inr assump_17 =>
        cases assump_17
        case inl assump_30 =>
          cases assump_15
          case inl assump_34 =>
            exact assump_9
          case inr assump_35 =>
            exact assump_9
        case inr assump_31 =>
          cases assump_15
          case inl assump_42 =>
            exact assump_9
          case inr assump_43 =>
            exact assump_9
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p1 p6 p0 p5 p4 : Prop)
theorem file65_94001 : (((((p1 → False) ∧ (False ∨ p1)) ∧ ((True → p5) ∨ (p4 ∨ p4))) ∧ (((p6 ∧ p0) ∨ (p6 ∨ p5)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          cases assump_5
          case inl assump_16 =>
            have assump_54 : p1 := by
              exact assump_11
            let assump_26 := assump_6 assump_54
            apply False.elim assump_26
          case inr assump_17 =>
            cases assump_17
            case inl assump_30 =>
              have assump_55 : p1 := by
                exact assump_11
              let assump_39 := assump_6 assump_55
              apply False.elim assump_39
            case inr assump_31 =>
              have assump_56 : p1 := by
                exact assump_11
              let assump_50 := assump_6 assump_56
              apply False.elim assump_50


variable (p4 p2 p0 p6 p3 p7 : Prop)
theorem file65_95143 : (((((p3 ∧ p7) → False) → False) ∧ (((p0 → False) ∨ (p2 ∧ p2)) → ((p2 ∨ p3) → False))) → ((((p3 → False) ∧ (p2 → False)) → ((p2 ∧ p4) → (p2 → False))) ∨ (((p6 ∨ p7) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      cases assump_8
      case intro assump_19 assump_20 =>
        have assump_29 : p2 := by
          exact assump_13
        let assump_25 := assump_20 assump_29
        apply False.elim assump_25


variable (p7 p3 p0 p4 p5 p1 p6 : Prop)
theorem file65_95797 : ((((((False ∨ p4) → (p5 ∧ True)) ∧ ((p3 ∨ True) ∧ (p6 → True))) → (((p1 ∨ p7) → False) → ((False ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∨ p4) → (p5 ∧ True)) ∧ ((p3 ∨ True) ∧ (p6 → True))) → (((p1 ∨ p7) → False) → ((False ∧ p0) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p4 p6 p0 : Prop)
theorem file65_96352 : (((((False ∧ p6) ∨ (p7 → False)) → ((p4 ∧ p0) → (p7 → p0))) → False) → False) := by
  intro assump_1
  have assump_27 : (((False ∧ p6) ∨ (p7 → False)) → ((p4 ∧ p0) → (p7 → p0))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
      case inr assump_17 =>
        exact assump_11
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p5 p3 p0 p4 p1 p6 p2 p7 : Prop)
theorem file65_96985 : ((((((p6 ∧ p6) ∨ (p7 → p5)) → ((p3 ∧ True) ∧ (p5 ∨ p1))) → False) ∧ ((((p0 ∧ p4) ∨ (False ∨ p2)) ∧ ((p6 → True) → False)) ∧ (((p1 ∧ p2) ∧ (p1 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_44 : (p6 → True) := by
              intro assump_24
              apply True.intro
            let assump_23 := assump_9 assump_44
            apply False.elim assump_23
        case inr assump_11 =>
          cases assump_11
          case inl assump_28 =>
            apply False.elim assump_28
          case inr assump_29 =>
            have assump_45 : (p6 → True) := by
              intro assump_40
              apply True.intro
            let assump_39 := assump_9 assump_45
            apply False.elim assump_39


variable (p6 p1 p7 p2 p5 p4 : Prop)
theorem file65_98077 : (((((True ∧ p4) → False) ∧ ((p5 → False) ∧ (p1 → p2))) → False) → ((((False ∧ False) ∧ (p5 → False)) ∧ ((p1 ∨ p6) → False)) → (((p7 → False) → False) ∨ ((p2 → p1) ∨ (p6 ∨ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p3 p6 p2 p7 p1 p0 p4 p5 : Prop)
theorem file65_98564 : (((((p7 ∨ p3) ∨ (False ∧ p2)) ∨ ((p4 ∨ p1) ∧ (p2 ∧ p2))) → (((True ∨ p1) → False) → ((p5 ∨ p5) → False))) ∨ ((((p0 → p4) → (p4 ∧ p6)) ∧ ((p4 ∧ p5) → False)) ∧ (((p5 ∧ False) → (p1 ∨ p6)) ∨ ((p4 ∧ p7) ∧ (p0 → False))))) := by
  apply Or.inl
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    cases assump_7
    case inl assump_16 =>
      cases assump_16
      case inl assump_18 =>
        cases assump_18
        case inl assump_20 =>
          have assump_136 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_25 := assump_8 assump_136
          apply False.elim assump_25
        case inr assump_21 =>
          have assump_137 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_32 := assump_8 assump_137
          apply False.elim assump_32
      case inr assump_19 =>
        cases assump_19
        case intro assump_36 assump_37 =>
          apply False.elim assump_36
    case inr assump_17 =>
      cases assump_17
      case intro assump_40 assump_41 =>
        cases assump_40
        case inl assump_42 =>
          cases assump_41
          case intro assump_46 assump_47 =>
            have assump_138 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_55 := assump_8 assump_138
            apply False.elim assump_55
        case inr assump_43 =>
          cases assump_41
          case intro assump_61 assump_62 =>
            have assump_139 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_70 := assump_8 assump_139
            apply False.elim assump_70
  case inr assump_11 =>
    cases assump_7
    case inl assump_78 =>
      cases assump_78
      case inl assump_80 =>
        cases assump_80
        case inl assump_82 =>
          have assump_140 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_87 := assump_8 assump_140
          apply False.elim assump_87
        case inr assump_83 =>
          have assump_141 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_94 := assump_8 assump_141
          apply False.elim assump_94
      case inr assump_81 =>
        cases assump_81
        case intro assump_98 assump_99 =>
          apply False.elim assump_98
    case inr assump_79 =>
      cases assump_79
      case intro assump_102 assump_103 =>
        cases assump_102
        case inl assump_104 =>
          cases assump_103
          case intro assump_108 assump_109 =>
            have assump_142 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_117 := assump_8 assump_142
            apply False.elim assump_117
        case inr assump_105 =>
          cases assump_103
          case intro assump_123 assump_124 =>
            have assump_143 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_132 := assump_8 assump_143
            apply False.elim assump_132


variable (p6 p1 p3 p0 p2 p5 : Prop)
theorem file65_101751 : (((((p6 ∧ p5) → (True ∧ p3)) ∧ ((True ∨ p0) → False)) → False) ∨ ((((False → p3) ∧ (p6 ∧ p1)) ∧ ((p2 → False) ∨ (True ∨ True))) → False)) := by
  apply Or.inl
  intro assump_82
  cases assump_82
  case intro assump_83 assump_84 =>
    have assump_93 : (True ∨ p0) := by
      apply Or.inl
      apply True.intro
    let assump_89 := assump_84 assump_93
    apply False.elim assump_89


variable (p0 p2 p6 p1 p7 p4 : Prop)
theorem file65_102195 : ((((((True ∨ p6) ∨ (p1 ∧ p7)) ∨ ((p6 ∨ p0) → False)) ∨ (((p0 ∧ False) ∧ (p2 → False)) ∧ ((p2 ∧ p7) → (p4 → p4)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p6) ∨ (p1 ∧ p7)) ∨ ((p6 ∨ p0) → False)) ∨ (((p0 ∧ False) ∧ (p2 → False)) ∧ ((p2 ∧ p7) → (p4 → p4)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p4 p1 p7 p3 p5 p0 : Prop)
theorem file65_102702 : (((((p1 ∨ True) ∧ (True ∧ p7)) → False) → False) → ((((p5 ∨ p7) ∨ (p4 ∨ True)) → ((p0 ∨ p7) ∨ (True ∨ p1))) ∨ (((p0 ∧ p5) ∧ (p5 ∧ p4)) ∧ ((p2 → p1) → (p3 ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inr
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply Or.inr
      exact assump_8
  case inr assump_6 =>
    cases assump_6
    case inl assump_13 =>
      apply Or.inr
      apply Or.inl
      apply True.intro
    case inr assump_14 =>
      apply Or.inr
      apply Or.inl
      apply True.intro


variable (p3 p4 p1 p7 : Prop)
theorem file65_103420 : ((((((p1 → False) ∨ (p3 → False)) → False) ∧ (((p4 → True) → (True → False)) ∨ ((p3 → False) → False))) ∧ ((((p3 → True) → False) → ((p1 ∧ p7) → (p7 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_46 : (((p3 → True) → False) → ((p1 ∧ p7) → (p7 ∨ p3))) := by
          intro assump_15
          intro assump_16
          cases assump_16
          case intro assump_17 assump_18 =>
            apply Or.inl
            exact assump_18
        let assump_14 := assump_3 assump_46
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_47 : (((p3 → True) → False) → ((p1 ∧ p7) → (p7 ∨ p3))) := by
          intro assump_33
          intro assump_34
          cases assump_34
          case intro assump_35 assump_36 =>
            apply Or.inl
            exact assump_36
        let assump_32 := assump_3 assump_47
        apply False.elim assump_32


variable (p0 p5 p1 p3 p2 p6 p4 : Prop)
theorem file65_104533 : ((((((p4 → True) → False) → False) → False) ∧ ((((p0 ∧ p2) ∨ (p3 ∧ p6)) ∧ ((False → False) → (p4 → False))) → (((p3 → False) ∧ (p4 ∨ p5)) → ((p1 ∨ p4) → (p3 ∧ p2))))) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    have assump_37 : (((p4 → True) → False) → False) := by
      intro assump_26
      have assump_38 : (p4 → True) := by
        intro assump_30
        apply True.intro
      let assump_29 := assump_26 assump_38
      apply False.elim assump_29
    let assump_25 := assump_18 assump_37
    apply False.elim assump_25


variable (p3 p1 p5 p6 p2 p7 p4 p0 : Prop)
theorem file65_105172 : (((((p6 ∨ False) → False) ∨ ((p7 ∧ p5) ∨ (True ∨ p0))) ∨ (((p2 ∧ p0) → (p1 ∨ p2)) ∧ ((p4 → False) ∧ (p7 → p3)))) → ((((p5 ∨ p0) ∨ (p3 ∧ False)) ∧ ((p0 → True) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            have assump_147 : (p0 → True) := by
              intro assump_21
              apply True.intro
            let assump_20 := assump_4 assump_147
            apply False.elim assump_20
          case inr assump_16 =>
            cases assump_16
            case inl assump_25 =>
              cases assump_25
              case intro assump_27 assump_28 =>
                have assump_148 : (p0 → True) := by
                  intro assump_36
                  apply True.intro
                let assump_35 := assump_4 assump_148
                apply False.elim assump_35
            case inr assump_26 =>
              cases assump_26
              case inl assump_40 =>
                have assump_149 : (p0 → True) := by
                  intro assump_45
                  apply True.intro
                let assump_44 := assump_4 assump_149
                apply False.elim assump_44
              case inr assump_41 =>
                have assump_150 : (p0 → True) := by
                  intro assump_53
                  apply True.intro
                let assump_52 := assump_4 assump_150
                apply False.elim assump_52
        case inr assump_14 =>
          cases assump_14
          case intro assump_57 assump_58 =>
            cases assump_58
            case intro assump_61 assump_62 =>
              have assump_151 : (p0 → True) := by
                intro assump_71
                apply True.intro
              let assump_70 := assump_4 assump_151
              apply False.elim assump_70
      case inr assump_8 =>
        cases assump_1
        case inl assump_79 =>
          cases assump_79
          case inl assump_81 =>
            have assump_152 : (p0 → True) := by
              intro assump_87
              apply True.intro
            let assump_86 := assump_4 assump_152
            apply False.elim assump_86
          case inr assump_82 =>
            cases assump_82
            case inl assump_91 =>
              cases assump_91
              case intro assump_93 assump_94 =>
                have assump_153 : (p0 → True) := by
                  intro assump_102
                  apply True.intro
                let assump_101 := assump_4 assump_153
                apply False.elim assump_101
            case inr assump_92 =>
              cases assump_92
              case inl assump_106 =>
                have assump_154 : (p0 → True) := by
                  intro assump_111
                  apply True.intro
                let assump_110 := assump_4 assump_154
                apply False.elim assump_110
              case inr assump_107 =>
                have assump_155 : (p0 → True) := by
                  intro assump_119
                  apply True.intro
                let assump_118 := assump_4 assump_155
                apply False.elim assump_118
        case inr assump_80 =>
          cases assump_80
          case intro assump_123 assump_124 =>
            cases assump_124
            case intro assump_127 assump_128 =>
              have assump_156 : (p0 → True) := by
                intro assump_137
                apply True.intro
              let assump_136 := assump_4 assump_156
              apply False.elim assump_136
    case inr assump_6 =>
      cases assump_6
      case intro assump_141 assump_142 =>
        apply False.elim assump_142


variable (p7 p6 p0 p3 p1 p5 p2 : Prop)
theorem file65_109063 : ((((((p2 ∨ p7) → (True ∨ p6)) → False) ∧ (((p2 ∨ p3) → (p6 → False)) → False)) ∧ ((((p6 → p6) → False) ∧ ((p2 → False) ∨ (p3 → False))) ∧ (((p6 ∧ p0) ∧ (p5 → False)) ∨ ((p1 ∨ p2) ∧ (p0 → p1))))) → False) := by
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      cases assump_32
      case intro assump_39 assump_40 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          cases assump_42
          case inl assump_45 =>
            cases assump_40
            case inl assump_49 =>
              cases assump_49
              case intro assump_51 assump_52 =>
                cases assump_51
                case intro assump_53 assump_54 =>
                  have assump_157 : (p6 → p6) := by
                    intro assump_66
                    exact assump_66
                  let assump_65 := assump_41 assump_157
                  apply False.elim assump_65
            case inr assump_50 =>
              cases assump_50
              case intro assump_72 assump_73 =>
                cases assump_72
                case inl assump_74 =>
                  have assump_158 : (p6 → p6) := by
                    intro assump_84
                    exact assump_84
                  let assump_83 := assump_41 assump_158
                  apply False.elim assump_83
                case inr assump_75 =>
                  have assump_159 : p2 := by
                    exact assump_75
                  let assump_96 := assump_45 assump_159
                  apply False.elim assump_96
          case inr assump_46 =>
            cases assump_40
            case inl assump_102 =>
              cases assump_102
              case intro assump_104 assump_105 =>
                cases assump_104
                case intro assump_106 assump_107 =>
                  have assump_160 : (p6 → p6) := by
                    intro assump_119
                    exact assump_119
                  let assump_118 := assump_41 assump_160
                  apply False.elim assump_118
            case inr assump_103 =>
              cases assump_103
              case intro assump_125 assump_126 =>
                cases assump_125
                case inl assump_127 =>
                  have assump_161 : (p6 → p6) := by
                    intro assump_137
                    exact assump_137
                  let assump_136 := assump_41 assump_161
                  apply False.elim assump_136
                case inr assump_128 =>
                  have assump_162 : (p6 → p6) := by
                    intro assump_151
                    exact assump_151
                  let assump_150 := assump_41 assump_162
                  apply False.elim assump_150


variable (p7 p3 p5 : Prop)
theorem file65_111889 : (((((True → False) → False) ∨ ((p3 → False) → False)) → False) → ((((True → p7) ∨ (p3 → False)) ∧ ((p5 ∧ p3) ∧ (p3 → False))) → False)) := by
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
          have assump_57 : (((True → False) → False) ∨ ((p3 → False) → False)) := by
            apply Or.inl
            intro assump_22
            have assump_58 : True := by
              apply True.intro
            let assump_25 := assump_22 assump_58
            apply False.elim assump_25
          let assump_21 := assump_1 assump_57
          apply False.elim assump_21
    case inr assump_6 =>
      cases assump_4
      case intro assump_34 assump_35 =>
        cases assump_34
        case intro assump_36 assump_37 =>
          have assump_59 : (((True → False) → False) ∨ ((p3 → False) → False)) := by
            apply Or.inl
            intro assump_47
            have assump_60 : True := by
              apply True.intro
            let assump_50 := assump_47 assump_60
            apply False.elim assump_50
          let assump_46 := assump_1 assump_59
          apply False.elim assump_46


variable (p4 p5 p7 p6 p0 p1 : Prop)
theorem file65_113257 : (((((p4 → p4) → False) ∧ ((p1 ∨ p6) ∨ (p7 ∨ p5))) → (((p1 → True) ∨ (p4 ∧ True)) → ((p7 → False) → (p1 ∧ p1)))) ∨ ((((False ∧ p4) → False) → False) ∧ (((False → False) → (True ∧ p6)) ∧ ((p5 → p0) → (True ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          exact assump_16
        case inr assump_17 =>
          have assump_196 : (p4 → p4) := by
            intro assump_24
            exact assump_24
          let assump_23 := assump_10 assump_196
          apply False.elim assump_23
      case inr assump_15 =>
        cases assump_15
        case inl assump_30 =>
          have assump_197 : (p4 → p4) := by
            intro assump_36
            exact assump_36
          let assump_35 := assump_10 assump_197
          apply False.elim assump_35
        case inr assump_31 =>
          have assump_198 : (p4 → p4) := by
            intro assump_46
            exact assump_46
          let assump_45 := assump_10 assump_198
          apply False.elim assump_45
  case inr assump_7 =>
    cases assump_7
    case intro assump_52 assump_53 =>
      cases assump_1
      case intro assump_58 assump_59 =>
        cases assump_59
        case inl assump_62 =>
          cases assump_62
          case inl assump_64 =>
            exact assump_64
          case inr assump_65 =>
            have assump_199 : (p4 → p4) := by
              intro assump_72
              exact assump_72
            let assump_71 := assump_58 assump_199
            apply False.elim assump_71
        case inr assump_63 =>
          cases assump_63
          case inl assump_78 =>
            have assump_200 : (p4 → p4) := by
              intro assump_84
              exact assump_84
            let assump_83 := assump_58 assump_200
            apply False.elim assump_83
          case inr assump_79 =>
            have assump_201 : (p4 → p4) := by
              intro assump_94
              exact assump_94
            let assump_93 := assump_58 assump_201
            apply False.elim assump_93
  cases assump_2
  case inl assump_102 =>
    cases assump_1
    case intro assump_106 assump_107 =>
      cases assump_107
      case inl assump_110 =>
        cases assump_110
        case inl assump_112 =>
          exact assump_112
        case inr assump_113 =>
          have assump_202 : (p4 → p4) := by
            intro assump_120
            exact assump_120
          let assump_119 := assump_106 assump_202
          apply False.elim assump_119
      case inr assump_111 =>
        cases assump_111
        case inl assump_126 =>
          have assump_203 : (p4 → p4) := by
            intro assump_132
            exact assump_132
          let assump_131 := assump_106 assump_203
          apply False.elim assump_131
        case inr assump_127 =>
          have assump_204 : (p4 → p4) := by
            intro assump_142
            exact assump_142
          let assump_141 := assump_106 assump_204
          apply False.elim assump_141
  case inr assump_103 =>
    cases assump_103
    case intro assump_148 assump_149 =>
      cases assump_1
      case intro assump_154 assump_155 =>
        cases assump_155
        case inl assump_158 =>
          cases assump_158
          case inl assump_160 =>
            exact assump_160
          case inr assump_161 =>
            have assump_205 : (p4 → p4) := by
              intro assump_168
              exact assump_168
            let assump_167 := assump_154 assump_205
            apply False.elim assump_167
        case inr assump_159 =>
          cases assump_159
          case inl assump_174 =>
            have assump_206 : (p4 → p4) := by
              intro assump_180
              exact assump_180
            let assump_179 := assump_154 assump_206
            apply False.elim assump_179
          case inr assump_175 =>
            have assump_207 : (p4 → p4) := by
              intro assump_190
              exact assump_190
            let assump_189 := assump_154 assump_207
            apply False.elim assump_189


variable (p0 p7 p3 p4 : Prop)
theorem file65_117564 : (((((True → False) → False) ∨ ((p3 → False) ∧ (p7 → p3))) → False) → ((((p0 ∨ p4) → False) → False) → False)) := by
  intro assump_5
  intro assump_6
  have assump_22 : (((True → False) → False) ∨ ((p3 → False) ∧ (p7 → p3))) := by
    apply Or.inl
    intro assump_12
    have assump_23 : True := by
      apply True.intro
    let assump_15 := assump_12 assump_23
    apply False.elim assump_15
  let assump_11 := assump_5 assump_22
  apply False.elim assump_11


variable (p2 p1 p5 p7 p0 p4 : Prop)
theorem file65_118086 : ((((((p2 ∧ p5) → False) → False) → (((p5 → False) → (p0 ∧ p4)) ∨ ((False ∧ p7) ∨ (p0 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p2 ∧ p5) → False) → False) → (((p5 → False) → (p0 ∧ p4)) ∨ ((False ∧ p7) ∨ (p0 ∨ p1)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    have assump_53 : ((p2 ∧ p5) → False) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        have assump_54 : p5 := by
          exact assump_15
        let assump_22 := assump_8 assump_54
        apply False.elim assump_22
    let assump_12 := assump_5 assump_53
    apply False.elim assump_12
    have assump_55 : ((p2 ∧ p5) → False) := by
      intro assump_33
      cases assump_33
      case intro assump_34 assump_35 =>
        have assump_56 : p5 := by
          exact assump_35
        let assump_42 := assump_8 assump_56
        apply False.elim assump_42
    let assump_32 := assump_5 assump_55
    apply False.elim assump_32
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p3 p7 p2 p0 p6 p5 : Prop)
theorem file65_119220 : (((((p7 → p7) → False) → ((p2 ∨ p2) → False)) → False) → ((((p6 ∨ p5) → False) ∨ ((p0 → p6) ∨ (p5 → False))) ∧ (((p0 → False) ∧ (True ∨ True)) ∧ ((p3 ∧ p3) ∧ (p2 → False))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_209 : (((p7 → p7) → False) → ((p2 ∨ p2) → False)) := by
      intro assump_11
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        have assump_210 : (p7 → p7) := by
          intro assump_20
          exact assump_20
        let assump_19 := assump_11 assump_210
        apply False.elim assump_19
      case inr assump_14 =>
        have assump_211 : (p7 → p7) := by
          intro assump_31
          exact assump_31
        let assump_30 := assump_11 assump_211
        apply False.elim assump_30
    let assump_10 := assump_1 assump_209
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_212 : (((p7 → p7) → False) → ((p2 ∨ p2) → False)) := by
      intro assump_44
      intro assump_45
      cases assump_45
      case inl assump_46 =>
        have assump_213 : (p7 → p7) := by
          intro assump_53
          exact assump_53
        let assump_52 := assump_44 assump_213
        apply False.elim assump_52
      case inr assump_47 =>
        have assump_214 : (p7 → p7) := by
          intro assump_64
          exact assump_64
        let assump_63 := assump_44 assump_214
        apply False.elim assump_63
    let assump_43 := assump_1 assump_212
    apply False.elim assump_43
  apply And.intro
  apply And.intro
  intro assump_73
  have assump_215 : (((p7 → p7) → False) → ((p2 ∨ p2) → False)) := by
    intro assump_79
    intro assump_80
    cases assump_80
    case inl assump_81 =>
      have assump_216 : (p7 → p7) := by
        intro assump_88
        exact assump_88
      let assump_87 := assump_79 assump_216
      apply False.elim assump_87
    case inr assump_82 =>
      have assump_217 : (p7 → p7) := by
        intro assump_99
        exact assump_99
      let assump_98 := assump_79 assump_217
      apply False.elim assump_98
  let assump_78 := assump_1 assump_215
  apply False.elim assump_78
  apply Or.inl
  apply True.intro
  apply And.intro
  apply And.intro
  have assump_218 : (((p7 → p7) → False) → ((p2 ∨ p2) → False)) := by
    intro assump_113
    intro assump_114
    cases assump_114
    case inl assump_115 =>
      have assump_219 : (p7 → p7) := by
        intro assump_122
        exact assump_122
      let assump_121 := assump_113 assump_219
      apply False.elim assump_121
    case inr assump_116 =>
      have assump_220 : (p7 → p7) := by
        intro assump_133
        exact assump_133
      let assump_132 := assump_113 assump_220
      apply False.elim assump_132
  let assump_112 := assump_1 assump_218
  apply False.elim assump_112
  have assump_221 : (((p7 → p7) → False) → ((p2 ∨ p2) → False)) := by
    intro assump_145
    intro assump_146
    cases assump_146
    case inl assump_147 =>
      have assump_222 : (p7 → p7) := by
        intro assump_154
        exact assump_154
      let assump_153 := assump_145 assump_222
      apply False.elim assump_153
    case inr assump_148 =>
      have assump_223 : (p7 → p7) := by
        intro assump_165
        exact assump_165
      let assump_164 := assump_145 assump_223
      apply False.elim assump_164
  let assump_144 := assump_1 assump_221
  apply False.elim assump_144
  intro assump_174
  have assump_224 : (((p7 → p7) → False) → ((p2 ∨ p2) → False)) := by
    intro assump_180
    intro assump_181
    cases assump_181
    case inl assump_182 =>
      have assump_225 : (p7 → p7) := by
        intro assump_189
        exact assump_189
      let assump_188 := assump_180 assump_225
      apply False.elim assump_188
    case inr assump_183 =>
      have assump_226 : (p7 → p7) := by
        intro assump_200
        exact assump_200
      let assump_199 := assump_180 assump_226
      apply False.elim assump_199
  let assump_179 := assump_1 assump_224
  apply False.elim assump_179


variable (p1 p7 p4 p3 p2 p5 p6 : Prop)
theorem file65_123340 : (((((False ∧ p3) ∨ (p3 ∨ p4)) ∧ ((True → False) ∧ (p3 → p2))) → False) ∨ ((((p3 ∨ p6) → (p7 → p1)) → False) → (((True → False) → False) ∧ ((p2 ∨ p5) → (p1 ∨ p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6
    case inr assump_5 =>
      cases assump_5
      case inl assump_10 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          have assump_39 : True := by
            apply True.intro
          let assump_22 := assump_14 assump_39
          apply False.elim assump_22
      case inr assump_11 =>
        cases assump_3
        case intro assump_28 assump_29 =>
          have assump_40 : True := by
            apply True.intro
          let assump_35 := assump_28 assump_40
          apply False.elim assump_35


variable (p3 p7 p5 p2 p1 p6 : Prop)
theorem file65_124325 : (((((True ∧ p7) → False) → ((p3 ∧ p7) → False)) → False) → ((((p7 → p5) ∧ (p5 → p6)) ∨ ((p7 → p6) ∧ (p1 ∨ p1))) → (((p2 ∨ p5) ∨ (p1 ∧ p1)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_252 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
            intro assump_21
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              have assump_253 : (True ∧ p7) := by
                apply And.intro
                apply True.intro
                exact assump_24
              let assump_31 := assump_21 assump_253
              apply False.elim assump_31
          let assump_20 := assump_1 assump_252
          apply False.elim assump_20
      case inr assump_11 =>
        cases assump_11
        case intro assump_38 assump_39 =>
          cases assump_39
          case inl assump_42 =>
            have assump_254 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_49
              intro assump_50
              cases assump_50
              case intro assump_51 assump_52 =>
                have assump_255 : (True ∧ p7) := by
                  apply And.intro
                  apply True.intro
                  exact assump_52
                let assump_59 := assump_49 assump_255
                apply False.elim assump_59
            let assump_48 := assump_1 assump_254
            apply False.elim assump_48
          case inr assump_43 =>
            have assump_256 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_71
              intro assump_72
              cases assump_72
              case intro assump_73 assump_74 =>
                have assump_257 : (True ∧ p7) := by
                  apply And.intro
                  apply True.intro
                  exact assump_74
                let assump_81 := assump_71 assump_257
                apply False.elim assump_81
            let assump_70 := assump_1 assump_256
            apply False.elim assump_70
    case inr assump_7 =>
      cases assump_2
      case inl assump_90 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          have assump_258 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
            intro assump_101
            intro assump_102
            cases assump_102
            case intro assump_103 assump_104 =>
              have assump_259 : (True ∧ p7) := by
                apply And.intro
                apply True.intro
                exact assump_104
              let assump_111 := assump_101 assump_259
              apply False.elim assump_111
          let assump_100 := assump_1 assump_258
          apply False.elim assump_100
      case inr assump_91 =>
        cases assump_91
        case intro assump_118 assump_119 =>
          cases assump_119
          case inl assump_122 =>
            have assump_260 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_129
              intro assump_130
              cases assump_130
              case intro assump_131 assump_132 =>
                have assump_261 : (True ∧ p7) := by
                  apply And.intro
                  apply True.intro
                  exact assump_132
                let assump_139 := assump_129 assump_261
                apply False.elim assump_139
            let assump_128 := assump_1 assump_260
            apply False.elim assump_128
          case inr assump_123 =>
            have assump_262 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_151
              intro assump_152
              cases assump_152
              case intro assump_153 assump_154 =>
                have assump_263 : (True ∧ p7) := by
                  apply And.intro
                  apply True.intro
                  exact assump_154
                let assump_161 := assump_151 assump_263
                apply False.elim assump_161
            let assump_150 := assump_1 assump_262
            apply False.elim assump_150
  case inr assump_5 =>
    cases assump_5
    case intro assump_168 assump_169 =>
      cases assump_2
      case inl assump_174 =>
        cases assump_174
        case intro assump_176 assump_177 =>
          have assump_264 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
            intro assump_185
            intro assump_186
            cases assump_186
            case intro assump_187 assump_188 =>
              have assump_265 : (True ∧ p7) := by
                apply And.intro
                apply True.intro
                exact assump_188
              let assump_195 := assump_185 assump_265
              apply False.elim assump_195
          let assump_184 := assump_1 assump_264
          apply False.elim assump_184
      case inr assump_175 =>
        cases assump_175
        case intro assump_202 assump_203 =>
          cases assump_203
          case inl assump_206 =>
            have assump_266 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_213
              intro assump_214
              cases assump_214
              case intro assump_215 assump_216 =>
                have assump_267 : (True ∧ p7) := by
                  apply And.intro
                  apply True.intro
                  exact assump_216
                let assump_223 := assump_213 assump_267
                apply False.elim assump_223
            let assump_212 := assump_1 assump_266
            apply False.elim assump_212
          case inr assump_207 =>
            have assump_268 : (((True ∧ p7) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_235
              intro assump_236
              cases assump_236
              case intro assump_237 assump_238 =>
                have assump_269 : (True ∧ p7) := by
                  apply And.intro
                  apply True.intro
                  exact assump_238
                let assump_245 := assump_235 assump_269
                apply False.elim assump_245
            let assump_234 := assump_1 assump_268
            apply False.elim assump_234


variable (p7 p0 p5 p4 p6 : Prop)
theorem file65_130721 : (((((p0 → True) ∨ (p5 → p6)) ∨ ((p4 ∨ p0) → (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p0 → True) ∨ (p5 → p6)) ∨ ((p4 ∨ p0) → (p7 → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p1 p7 p5 p2 p0 : Prop)
theorem file65_131097 : ((((((p5 ∧ p7) ∧ (p1 ∨ p2)) ∨ ((True ∧ False) → (True ∧ p1))) ∨ (((p0 → False) → False) → ((p0 → False) ∧ (p7 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p5 ∧ p7) ∧ (p1 ∨ p2)) ∨ ((True ∧ False) → (True ∧ p1))) ∨ (((p0 → False) → False) → ((p0 → False) ∧ (p7 ∨ True)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply And.intro
    apply True.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p4 p2 p1 p5 p7 p3 p0 : Prop)
theorem file65_131715 : (((((p6 → p1) ∨ (p5 → False)) ∨ ((False → False) ∨ (p2 ∨ p5))) → False) → ((((True ∧ p4) ∨ (p4 ∨ p3)) ∨ ((False → p4) ∨ (p7 → p0))) ∨ (((p2 → p0) ∨ (p4 → p3)) ∧ ((p2 ∨ p6) → (p6 → p4))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p2 p0 p5 p3 p4 p1 : Prop)
theorem file65_132076 : (((((p5 ∧ p5) ∨ (p0 ∨ True)) ∧ ((p1 → p1) → False)) ∨ (((p5 → False) → False) → ((False ∧ p1) → (p3 ∧ p0)))) → ((((p2 → p2) → (p4 ∧ p1)) → ((p4 ∧ p0) ∧ (p5 → False))) → (((p1 → False) ∧ (p2 → False)) → ((p1 ∨ True) ∨ (False ∧ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
        case inr assump_17 =>
          cases assump_17
          case inl assump_26 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
          case inr assump_27 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
    case inr assump_13 =>
      apply Or.inl
      apply Or.inr
      apply True.intro


variable (p0 p6 p2 p5 p7 p1 : Prop)
theorem file65_133153 : (((((True ∨ p7) → False) ∨ ((p5 → False) ∧ (p0 ∧ p1))) → (((p2 → p0) ∨ (p2 → False)) ∨ ((p0 → False) ∧ (p7 ∨ p6)))) ∨ ((((p6 → False) ∧ (p2 → False)) → False) ∧ (((p7 ∨ p5) → (p6 → False)) ∧ ((p0 → False) ∧ (p1 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    have assump_27 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_10 := assump_2 assump_27
    apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply Or.inl
        apply Or.inl
        intro assump_24
        exact assump_18


variable (p3 p7 : Prop)
theorem file65_133937 : ((((((p3 → True) ∨ (p7 ∧ False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p3 → True) ∨ (p7 ∧ False)) → False) → False) := by
    intro assump_5
    have assump_17 : ((p3 → True) ∨ (p7 ∧ False)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p7 p5 p2 p1 p6 p0 : Prop)
theorem file65_134438 : ((((((True → False) ∧ (p7 → p6)) → ((p5 → p3) → (p1 → p2))) ∨ (((p2 → p6) ∨ (p1 ∧ p0)) ∨ ((False → False) → False))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((True → False) ∧ (p7 → p6)) → ((p5 → p3) → (p1 → p2))) ∨ (((p2 → p6) ∨ (p1 ∧ p0)) ∨ ((False → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      have assump_27 : True := by
        apply True.intro
      let assump_19 := assump_12 assump_27
      apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p3 p6 p5 : Prop)
theorem file65_135118 : (((((p6 → p6) → False) → ((p5 ∨ p3) ∨ (p3 → False))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p6 → p6) → False) → ((p5 ∨ p3) ∨ (p3 → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_23 : (p6 → p6) := by
      intro assump_13
      exact assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p1 p7 p5 p2 p0 p4 p3 : Prop)
theorem file65_135626 : ((((((p5 → False) ∧ (True → False)) → ((p1 ∨ p3) ∧ (p0 → False))) → False) ∧ ((((p3 → False) ∨ (p4 → False)) ∧ ((p2 ∧ p5) ∨ (False ∧ p3))) ∧ (((p1 ∨ p4) ∨ (p0 ∨ p6)) → ((p4 → False) ∨ (p7 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              have assump_108 : (((p5 → False) ∧ (True → False)) → ((p1 ∨ p3) ∧ (p0 → False))) := by
                intro assump_29
                apply And.intro
                cases assump_29
                case intro assump_30 assump_31 =>
                  have assump_109 : True := by
                    apply True.intro
                  let assump_36 := assump_31 assump_109
                  apply False.elim assump_36
                intro assump_40
                cases assump_29
                case intro assump_43 assump_44 =>
                  have assump_110 : True := by
                    apply True.intro
                  let assump_49 := assump_44 assump_110
                  apply False.elim assump_49
              let assump_28 := assump_2 assump_108
              apply False.elim assump_28
          case inr assump_15 =>
            cases assump_15
            case intro assump_56 assump_57 =>
              apply False.elim assump_56
        case inr assump_11 =>
          cases assump_9
          case inl assump_62 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              have assump_111 : (((p5 → False) ∧ (True → False)) → ((p1 ∨ p3) ∧ (p0 → False))) := by
                intro assump_77
                apply And.intro
                cases assump_77
                case intro assump_78 assump_79 =>
                  have assump_112 : True := by
                    apply True.intro
                  let assump_84 := assump_79 assump_112
                  apply False.elim assump_84
                intro assump_88
                cases assump_77
                case intro assump_91 assump_92 =>
                  have assump_113 : True := by
                    apply True.intro
                  let assump_97 := assump_92 assump_113
                  apply False.elim assump_97
              let assump_76 := assump_2 assump_111
              apply False.elim assump_76
          case inr assump_63 =>
            cases assump_63
            case intro assump_104 assump_105 =>
              apply False.elim assump_104


variable (p7 p1 p2 p0 p5 p6 p4 : Prop)
theorem file65_138375 : ((((((p2 → p6) ∨ (p5 ∧ p6)) ∨ ((True → p5) ∨ (p4 → p7))) → (((p1 ∨ p2) ∧ (p6 → p6)) → False)) ∧ ((((True ∧ p0) → False) → False) ∧ (((True ∨ False) ∨ (p0 ∧ p5)) ∧ ((p1 ∨ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            have assump_51 : ((True ∧ p0) → False) := by
              intro assump_22
              cases assump_22
              case intro assump_23 assump_24 =>
                have assump_52 : (p1 ∨ p0) := by
                  apply Or.inr
                  exact assump_24
                let assump_30 := assump_11 assump_52
                apply False.elim assump_30
            let assump_21 := assump_6 assump_51
            apply False.elim assump_21
          case inr assump_15 =>
            apply False.elim assump_15
        case inr assump_13 =>
          cases assump_13
          case intro assump_39 assump_40 =>
            have assump_53 : (p1 ∨ p0) := by
              apply Or.inr
              exact assump_39
            let assump_47 := assump_11 assump_53
            apply False.elim assump_47


variable (p5 p1 p4 p6 p2 p7 : Prop)
theorem file65_139755 : ((((((True ∧ p6) → False) → ((p2 → False) → (p4 ∧ p5))) ∧ (((p5 ∧ p4) → (False ∧ p1)) ∨ ((p4 ∨ False) ∨ (p5 ∨ p2)))) ∧ ((((False → p7) → False) → False) → False)) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_17
      case inl assump_20 =>
        have assump_102 : (((False → p7) → False) → False) := by
          intro assump_27
          have assump_103 : (False → p7) := by
            intro assump_31
            apply False.elim assump_31
          let assump_30 := assump_27 assump_103
          apply False.elim assump_30
        let assump_26 := assump_15 assump_102
        apply False.elim assump_26
      case inr assump_21 =>
        cases assump_21
        case inl assump_40 =>
          cases assump_40
          case inl assump_42 =>
            have assump_104 : (((False → p7) → False) → False) := by
              intro assump_49
              have assump_105 : (False → p7) := by
                intro assump_53
                apply False.elim assump_53
              let assump_52 := assump_49 assump_105
              apply False.elim assump_52
            let assump_48 := assump_15 assump_104
            apply False.elim assump_48
          case inr assump_43 =>
            apply False.elim assump_43
        case inr assump_41 =>
          cases assump_41
          case inl assump_64 =>
            have assump_106 : (((False → p7) → False) → False) := by
              intro assump_71
              have assump_107 : (False → p7) := by
                intro assump_75
                apply False.elim assump_75
              let assump_74 := assump_71 assump_107
              apply False.elim assump_74
            let assump_70 := assump_15 assump_106
            apply False.elim assump_70
          case inr assump_65 =>
            have assump_108 : (((False → p7) → False) → False) := by
              intro assump_89
              have assump_109 : (False → p7) := by
                intro assump_93
                apply False.elim assump_93
              let assump_92 := assump_89 assump_109
              apply False.elim assump_92
            let assump_88 := assump_15 assump_108
            apply False.elim assump_88


variable (p3 p1 p5 p0 p2 p7 : Prop)
theorem file65_142096 : ((((((p1 ∨ p3) ∧ (p7 ∨ p2)) ∧ ((p0 ∨ p5) ∧ (p0 ∧ False))) → (((p2 → p7) → False) ∧ ((p1 → False) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_216 : ((((p1 ∨ p3) ∧ (p7 ∨ p2)) ∧ ((p0 ∨ p5) ∧ (p0 ∧ False))) → (((p2 → p7) → False) ∧ ((p1 → False) ∨ (True → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            cases assump_10
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                cases assump_22
                case intro assump_27 assump_28 =>
                  apply False.elim assump_28
              case inr assump_24 =>
                cases assump_22
                case intro assump_35 assump_36 =>
                  apply False.elim assump_36
          case inr assump_18 =>
            cases assump_10
            case intro assump_43 assump_44 =>
              cases assump_43
              case inl assump_45 =>
                cases assump_44
                case intro assump_49 assump_50 =>
                  apply False.elim assump_50
              case inr assump_46 =>
                cases assump_44
                case intro assump_57 assump_58 =>
                  apply False.elim assump_58
        case inr assump_14 =>
          cases assump_12
          case inl assump_65 =>
            cases assump_10
            case intro assump_69 assump_70 =>
              cases assump_69
              case inl assump_71 =>
                cases assump_70
                case intro assump_75 assump_76 =>
                  apply False.elim assump_76
              case inr assump_72 =>
                cases assump_70
                case intro assump_83 assump_84 =>
                  apply False.elim assump_84
          case inr assump_66 =>
            cases assump_10
            case intro assump_91 assump_92 =>
              cases assump_91
              case inl assump_93 =>
                cases assump_92
                case intro assump_97 assump_98 =>
                  apply False.elim assump_98
              case inr assump_94 =>
                cases assump_92
                case intro assump_105 assump_106 =>
                  apply False.elim assump_106
    cases assump_5
    case intro assump_111 assump_112 =>
      cases assump_111
      case intro assump_113 assump_114 =>
        cases assump_113
        case inl assump_115 =>
          cases assump_114
          case inl assump_119 =>
            cases assump_112
            case intro assump_123 assump_124 =>
              cases assump_123
              case inl assump_125 =>
                cases assump_124
                case intro assump_129 assump_130 =>
                  apply False.elim assump_130
              case inr assump_126 =>
                cases assump_124
                case intro assump_137 assump_138 =>
                  apply False.elim assump_138
          case inr assump_120 =>
            cases assump_112
            case intro assump_145 assump_146 =>
              cases assump_145
              case inl assump_147 =>
                cases assump_146
                case intro assump_151 assump_152 =>
                  apply False.elim assump_152
              case inr assump_148 =>
                cases assump_146
                case intro assump_159 assump_160 =>
                  apply False.elim assump_160
        case inr assump_116 =>
          cases assump_114
          case inl assump_167 =>
            cases assump_112
            case intro assump_171 assump_172 =>
              cases assump_171
              case inl assump_173 =>
                cases assump_172
                case intro assump_177 assump_178 =>
                  apply False.elim assump_178
              case inr assump_174 =>
                cases assump_172
                case intro assump_185 assump_186 =>
                  apply False.elim assump_186
          case inr assump_168 =>
            cases assump_112
            case intro assump_193 assump_194 =>
              cases assump_193
              case inl assump_195 =>
                cases assump_194
                case intro assump_199 assump_200 =>
                  apply False.elim assump_200
              case inr assump_196 =>
                cases assump_194
                case intro assump_207 assump_208 =>
                  apply False.elim assump_208
  let assump_4 := assump_1 assump_216
  apply False.elim assump_4


variable (p0 p2 p7 p4 p5 p1 : Prop)
theorem file65_146856 : (((((p7 → True) → False) → False) → False) → ((((p2 ∧ p1) ∨ (False → False)) → ((p4 ∨ p5) ∧ (p1 ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_19 : (((p7 → True) → False) → False) := by
    intro assump_8
    have assump_20 : (p7 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_8 assump_20
    apply False.elim assump_11
  let assump_7 := assump_1 assump_19
  apply False.elim assump_7


variable (p0 p4 p5 p7 p6 p1 p2 p3 : Prop)
theorem file65_147372 : (((((p6 ∧ p7) ∧ (p5 → p4)) ∧ ((p4 ∨ p3) ∧ (p3 ∨ p7))) ∨ (((p1 ∧ p3) → (p2 ∨ p2)) → False)) → ((((p6 ∧ p4) ∨ (p1 ∨ True)) → False) → (((p2 → False) ∨ (p1 ∨ p7)) ∨ ((p2 → False) ∧ (p0 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_8
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_20
              case inl assump_25 =>
                apply Or.inl
                apply Or.inl
                intro assump_29
                have assump_108 : ((p6 ∧ p4) ∨ (p1 ∨ True)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_11
                  exact assump_21
                let assump_38 := assump_2 assump_108
                apply False.elim assump_38
              case inr assump_26 =>
                apply Or.inl
                apply Or.inl
                intro assump_44
                have assump_109 : ((p6 ∧ p4) ∨ (p1 ∨ True)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_11
                  exact assump_21
                let assump_53 := assump_2 assump_109
                apply False.elim assump_53
            case inr assump_22 =>
              cases assump_20
              case inl assump_59 =>
                apply Or.inl
                apply Or.inl
                intro assump_63
                have assump_110 : ((p6 ∧ p4) ∨ (p1 ∨ True)) := by
                  apply Or.inr
                  apply Or.inr
                  apply True.intro
                let assump_72 := assump_2 assump_110
                apply False.elim assump_72
              case inr assump_60 =>
                apply Or.inl
                apply Or.inl
                intro assump_78
                have assump_111 : ((p6 ∧ p4) ∨ (p1 ∨ True)) := by
                  apply Or.inr
                  apply Or.inr
                  apply True.intro
                let assump_87 := assump_2 assump_111
                apply False.elim assump_87
  case inr assump_6 =>
    apply Or.inl
    apply Or.inl
    intro assump_93
    have assump_112 : ((p1 ∧ p3) → (p2 ∨ p2)) := by
      intro assump_98
      cases assump_98
      case intro assump_99 assump_100 =>
        apply Or.inl
        exact assump_93
    let assump_97 := assump_6 assump_112
    apply False.elim assump_97


variable (p3 p2 p5 p1 p0 p7 : Prop)
theorem file65_150055 : (((((False ∧ p7) → (p1 → p3)) → False) → False) ∨ ((((False ∨ p7) → False) ∧ ((p1 → p5) → False)) ∨ (((p5 ∧ True) → False) ∧ ((p0 ∨ p2) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_16 : ((False ∧ p7) → (p1 → p3)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p3 p7 p6 p0 p1 p5 p4 : Prop)
theorem file65_150550 : ((((((False → False) ∨ (p7 ∨ p7)) ∧ ((p1 → False) → (p3 → p3))) ∧ (((False ∨ p3) → False) ∧ ((p6 ∨ p4) → False))) ∧ ((((p2 → False) ∧ (p5 ∧ False)) ∧ ((p1 ∨ p4) ∧ (p7 ∧ p5))) ∧ (((False → False) → (p0 ∧ p5)) ∧ ((p3 → False) → False)))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_13
          case intro assump_22 assump_23 =>
            cases assump_11
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  cases assump_33
                  case intro assump_36 assump_37 =>
                    apply False.elim assump_37
        case inr assump_17 =>
          cases assump_17
          case inl assump_42 =>
            cases assump_13
            case intro assump_48 assump_49 =>
              cases assump_11
              case intro assump_54 assump_55 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  cases assump_56
                  case intro assump_58 assump_59 =>
                    cases assump_59
                    case intro assump_62 assump_63 =>
                      apply False.elim assump_63
          case inr assump_43 =>
            cases assump_13
            case intro assump_72 assump_73 =>
              cases assump_11
              case intro assump_78 assump_79 =>
                cases assump_78
                case intro assump_80 assump_81 =>
                  cases assump_80
                  case intro assump_82 assump_83 =>
                    cases assump_83
                    case intro assump_86 assump_87 =>
                      apply False.elim assump_87


variable (p0 p1 p7 : Prop)
theorem file65_152571 : ((((((p7 → True) → (False → p7)) → ((p1 ∧ False) ∧ (p0 → True))) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p7 → True) → (False → p7)) → ((p1 ∧ False) ∧ (p0 → True))) → False) := by
    intro assump_5
    have assump_23 : ((p7 → True) → (False → p7)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_23
    let assump_13 := And.left assump_8
    let assump_14 := And.right assump_13
    apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p5 p2 p7 p6 p1 : Prop)
theorem file65_153209 : (((((True → p1) ∧ (False → p5)) ∧ ((p6 → p3) ∧ (False ∧ p1))) ∧ (((p7 → p2) → (p3 ∨ p2)) → False)) → False) := by
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
          case intro assump_16 assump_17 =>
            apply False.elim assump_16


variable (p4 p3 p6 : Prop)
theorem file65_153730 : ((((((True ∨ p3) → False) ∨ ((p4 → False) ∧ (p6 → False))) → False) ∧ ((((p3 → p6) → (p3 → p3)) → False) ∨ (((True → False) → (True → p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_36 : ((p3 → p6) → (p3 → p3)) := by
        intro assump_11
        intro assump_12
        exact assump_12
      let assump_10 := assump_6 assump_36
      apply False.elim assump_10
    case inr assump_7 =>
      have assump_37 : ((True → False) → (True → p3)) := by
        intro assump_23
        intro assump_24
        have assump_38 : True := by
          apply True.intro
        let assump_29 := assump_23 assump_38
        apply False.elim assump_29
      let assump_22 := assump_7 assump_37
      apply False.elim assump_22


variable (p4 p6 p3 p7 : Prop)
theorem file65_154612 : ((((((True ∧ p4) → False) ∨ ((p3 ∨ p7) → False)) → (((p7 → p6) → False) → ((p7 → True) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((True ∧ p4) → False) ∨ ((p3 ∨ p7) → False)) → (((p7 → p6) → False) → ((p7 → True) → (p6 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_5
    case inl assump_15 =>
      have assump_41 : (p7 → p6) := by
        intro assump_21
        exact assump_8
      let assump_20 := assump_6 assump_41
      apply False.elim assump_20
    case inr assump_16 =>
      have assump_42 : (p7 → p6) := by
        intro assump_31
        exact assump_8
      let assump_30 := assump_6 assump_42
      apply False.elim assump_30
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p4 p3 p7 p2 p5 p1 p6 p0 : Prop)
theorem file65_155486 : (((((p4 → False) → False) → ((True → False) → False)) ∧ (((p0 ∨ p1) → (p4 ∨ p5)) → ((p2 ∧ p0) → False))) → ((((True ∨ p6) ∧ (p5 ∨ p7)) → ((False ∧ p4) → (p6 ∨ p4))) ∨ (((p3 → p5) ∨ (p7 ∧ p3)) → ((p7 ∨ p6) → (p1 → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10


variable (p3 p4 p7 p2 p0 p1 : Prop)
theorem file65_155988 : ((((((p7 → p1) ∨ (p1 ∧ False)) → False) ∧ (((p4 ∧ p0) → False) ∨ ((p2 ∨ p3) → (p1 ∨ True)))) ∧ ((((p1 → False) → (p1 → False)) ∨ ((p1 → p0) ∨ (p3 ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_46 : (((p1 → False) → (p1 → False)) ∨ ((p1 → p0) ∨ (p3 ∨ True))) := by
          apply Or.inl
          intro assump_15
          intro assump_16
          have assump_47 : p1 := by
            exact assump_16
          let assump_21 := assump_15 assump_47
          apply False.elim assump_21
        let assump_14 := assump_3 assump_46
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_48 : (((p1 → False) → (p1 → False)) ∨ ((p1 → p0) ∨ (p3 ∨ True))) := by
          apply Or.inl
          intro assump_33
          intro assump_34
          have assump_49 : p1 := by
            exact assump_34
          let assump_39 := assump_33 assump_49
          apply False.elim assump_39
        let assump_32 := assump_3 assump_48
        apply False.elim assump_32


variable (p2 p6 p0 p7 p1 p5 p4 : Prop)
theorem file65_157216 : (((((True ∧ p6) → (p0 → False)) → False) ∧ (((p1 → p1) → (p7 → False)) ∧ ((p6 ∨ False) → False))) → ((((p5 ∧ p2) ∨ (False → True)) → ((p4 ∧ p5) ∧ (True ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_41 : ((True ∧ p6) → (p0 → False)) := by
        intro assump_22
        intro assump_23
        cases assump_22
        case intro assump_26 assump_27 =>
          have assump_42 : (p6 ∨ False) := by
            apply Or.inl
            exact assump_27
          let assump_34 := assump_10 assump_42
          apply False.elim assump_34
      let assump_21 := assump_5 assump_41
      apply False.elim assump_21


variable (p1 p7 p4 p2 p0 p3 p5 : Prop)
theorem file65_158029 : (((((True → p4) ∧ (p5 → False)) → ((p0 ∧ p3) → (p4 ∧ True))) → False) → ((((p7 ∧ p4) ∧ (p0 ∨ p2)) → ((p3 → False) → (p1 ∨ True))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_28 : (((True → p4) ∧ (p5 → False)) → ((p0 ∧ p3) → (p4 ∧ True))) := by
    intro assump_8
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_8
      case intro assump_16 assump_17 =>
        have assump_29 : True := by
          apply True.intro
        let assump_23 := assump_16 assump_29
        exact assump_23
    apply True.intro
  let assump_7 := assump_1 assump_28
  apply False.elim assump_7


variable (p3 p4 p7 p5 p6 p0 p1 : Prop)
theorem file65_158750 : (((((False → False) ∨ (False ∧ p7)) ∧ ((p3 ∨ True) ∨ (False ∨ p0))) ∨ (((p3 → False) → (p0 ∨ p6)) → ((p1 ∧ p6) ∧ (p5 → False)))) ∨ ((((True → p6) ∧ (p3 → p1)) ∧ ((p0 → p4) ∨ (p3 ∧ True))) → (((p4 → False) ∨ (p0 ∨ p7)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  apply False.elim assump_1
  apply Or.inl
  apply Or.inr
  apply True.intro


