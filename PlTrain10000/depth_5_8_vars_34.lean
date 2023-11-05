variable (p0 p6 p1 p4 p7 p2 : Prop)
theorem file34_44 : (((((p1 ∨ p4) ∨ (p7 → p7)) → False) → False) ∨ ((((p2 ∧ True) → False) ∧ ((True → p2) → (p0 ∧ p6))) ∨ (((p7 ∨ True) ∨ (p6 ∧ p0)) → ((p4 ∨ p1) → (p6 ∧ p2))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p1 ∨ p4) ∨ (p7 → p7)) := by
    apply Or.inr
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 : Prop)
theorem file34_454 : ((((((False → False) ∧ (p2 → p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → False) ∧ (p2 → p2)) → False) → False) := by
    intro assump_5
    have assump_22 : ((False → False) ∧ (p2 → p2)) := by
      apply And.intro
      intro assump_9
      apply False.elim assump_9
      intro assump_12
      exact assump_12
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p6 p1 p2 p3 p4 p0 : Prop)
theorem file34_1011 : (((((p3 → False) ∨ (p2 ∧ False)) ∧ ((p3 ∨ p0) → False)) → (((p2 → True) → False) → False)) ∨ ((((p0 ∨ p6) ∨ (p4 ∧ False)) → ((p6 → p1) ∧ (p1 ∧ p4))) → False)) := by
  apply Or.inl
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    cases assump_13
    case inl assump_15 =>
      have assump_34 : (p2 → True) := by
        intro assump_24
        apply True.intro
      let assump_23 := assump_10 assump_34
      apply False.elim assump_23
    case inr assump_16 =>
      cases assump_16
      case intro assump_28 assump_29 =>
        apply False.elim assump_29


variable (p1 p5 p0 p7 p6 p4 : Prop)
theorem file34_1674 : ((((((p7 ∧ p6) ∧ (p7 → p6)) ∨ ((True ∨ p6) ∨ (p5 → False))) ∨ (((p5 → p0) ∧ (False → p7)) ∧ ((p1 → False) → (p4 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p7 ∧ p6) ∧ (p7 → p6)) ∨ ((True ∨ p6) ∨ (p5 → False))) ∨ (((p5 → p0) ∧ (False → p7)) ∧ ((p1 → False) → (p4 ∧ False)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p5 p1 p0 p7 p2 p6 : Prop)
theorem file34_2201 : (((((p0 ∧ False) → (False ∧ p5)) → False) ∧ (((False → False) ∨ (p2 ∧ False)) → ((False ∨ p6) ∨ (p0 ∨ p2)))) → ((((p3 ∧ p7) → (p7 ∨ True)) ∨ ((p7 ∧ p7) ∧ (p1 → False))) ∨ (((p6 → False) → (p1 → False)) ∧ ((p1 ∨ p7) ∨ (p3 ∨ p7))))) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    apply Or.inl
    apply Or.inl
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      apply Or.inl
      exact assump_21


variable (p5 p0 p6 p7 p4 : Prop)
theorem file34_2720 : (((((p0 ∨ p5) ∨ (True ∨ p5)) → False) → False) ∨ ((((p5 ∧ p5) → (p6 → p7)) → ((p0 → False) → (False ∧ p7))) ∧ (((p4 ∨ p6) ∧ (p0 → False)) → ((p0 ∨ p5) ∨ (p7 → False))))) := by
  apply Or.inl
  intro assump_53
  have assump_60 : ((p0 ∨ p5) ∨ (True ∨ p5)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_56 := assump_53 assump_60
  apply False.elim assump_56


variable (p1 p3 p5 p6 p7 p0 : Prop)
theorem file34_3163 : (((((False → False) ∨ (p6 → False)) ∨ ((p7 ∧ True) ∧ (p1 ∧ p0))) → False) → ((((p6 ∨ p0) → (p6 ∨ True)) → ((p0 → False) ∨ (p1 ∨ p6))) → (((True → False) ∧ (p7 ∨ p5)) ∧ ((False → p1) ∧ (True ∨ p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  intro assump_3
  have assump_35 : (((False → False) ∨ (p6 → False)) ∨ ((p7 ∧ True) ∧ (p1 ∧ p0))) := by
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_1 assump_35
  apply False.elim assump_10
  have assump_36 : (((False → False) ∨ (p6 → False)) ∨ ((p7 ∧ True) ∧ (p1 ∧ p0))) := by
    apply Or.inl
    apply Or.inl
    intro assump_22
    apply False.elim assump_22
  let assump_21 := assump_1 assump_36
  apply False.elim assump_21
  apply And.intro
  intro assump_28
  apply False.elim assump_28
  apply Or.inl
  apply True.intro


variable (p3 p5 p6 p4 p1 p2 p7 : Prop)
theorem file34_4098 : (((((p2 → False) → False) → ((p5 ∧ False) → (p5 → False))) ∧ (((True ∨ p2) ∨ (p6 → False)) ∨ ((True → False) ∧ (p2 → False)))) ∨ ((((p2 → p3) → False) ∧ ((False ∧ p2) ∨ (p1 ∨ p3))) ∨ (((p7 ∨ p3) ∨ (False ∨ p4)) ∧ ((p2 → False) → False)))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p3 p0 p4 p5 p7 p6 : Prop)
theorem file34_4632 : (((((True ∨ p3) ∨ (p4 ∨ p0)) → False) → False) ∨ ((((p4 ∨ p5) ∧ (p3 ∧ p7)) ∨ ((p6 ∨ p3) ∧ (p5 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∨ p3) ∨ (p4 ∨ p0)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p3 p4 p5 p6 : Prop)
theorem file34_5010 : ((((((True → False) ∧ (p4 → p3)) ∧ ((p1 → False) ∧ (p6 ∨ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_41 : ((((True → False) ∧ (p4 → p3)) ∧ ((p1 → False) ∧ (p6 ∨ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case inl assump_18 =>
            have assump_42 : True := by
              apply True.intro
            let assump_25 := assump_8 assump_42
            apply False.elim assump_25
          case inr assump_19 =>
            have assump_43 : True := by
              apply True.intro
            let assump_34 := assump_8 assump_43
            apply False.elim assump_34
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p2 p3 p6 p1 p5 p7 p4 : Prop)
theorem file34_5950 : (((((p4 ∧ p3) ∨ (p4 ∧ p6)) ∧ ((p2 ∨ p6) ∨ (p3 → True))) ∧ (((True → False) ∧ (p5 ∧ p5)) ∧ ((p3 ∨ p2) ∧ (False → p2)))) → ((((p6 ∨ True) ∧ (p2 ∨ p4)) → ((p6 ∧ p6) → False)) → (((p1 ∧ p7) ∨ (p1 → False)) ∧ ((p1 ∨ p4) ∧ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_8
          case inl assump_17 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_6
              case intro assump_23 assump_24 =>
                cases assump_23
                case intro assump_25 assump_26 =>
                  cases assump_26
                  case intro assump_29 assump_30 =>
                    cases assump_24
                    case intro assump_35 assump_36 =>
                      cases assump_35
                      case inl assump_37 =>
                        apply Or.inr
                        intro assump_43
                        have assump_798 : True := by
                          apply True.intro
                        let assump_51 := assump_25 assump_798
                        apply False.elim assump_51
                      case inr assump_38 =>
                        apply Or.inr
                        intro assump_59
                        have assump_799 : True := by
                          apply True.intro
                        let assump_67 := assump_25 assump_799
                        apply False.elim assump_67
            case inr assump_20 =>
              cases assump_6
              case intro assump_73 assump_74 =>
                cases assump_73
                case intro assump_75 assump_76 =>
                  cases assump_76
                  case intro assump_79 assump_80 =>
                    cases assump_74
                    case intro assump_85 assump_86 =>
                      cases assump_85
                      case inl assump_87 =>
                        apply Or.inr
                        intro assump_93
                        have assump_800 : True := by
                          apply True.intro
                        let assump_101 := assump_75 assump_800
                        apply False.elim assump_101
                      case inr assump_88 =>
                        apply Or.inr
                        intro assump_109
                        have assump_801 : True := by
                          apply True.intro
                        let assump_117 := assump_75 assump_801
                        apply False.elim assump_117
          case inr assump_18 =>
            cases assump_6
            case intro assump_123 assump_124 =>
              cases assump_123
              case intro assump_125 assump_126 =>
                cases assump_126
                case intro assump_129 assump_130 =>
                  cases assump_124
                  case intro assump_135 assump_136 =>
                    cases assump_135
                    case inl assump_137 =>
                      apply Or.inr
                      intro assump_143
                      have assump_802 : True := by
                        apply True.intro
                      let assump_151 := assump_125 assump_802
                      apply False.elim assump_151
                    case inr assump_138 =>
                      apply Or.inr
                      intro assump_159
                      have assump_803 : True := by
                        apply True.intro
                      let assump_167 := assump_125 assump_803
                      apply False.elim assump_167
      case inr assump_10 =>
        cases assump_10
        case intro assump_171 assump_172 =>
          cases assump_8
          case inl assump_177 =>
            cases assump_177
            case inl assump_179 =>
              cases assump_6
              case intro assump_183 assump_184 =>
                cases assump_183
                case intro assump_185 assump_186 =>
                  cases assump_186
                  case intro assump_189 assump_190 =>
                    cases assump_184
                    case intro assump_195 assump_196 =>
                      cases assump_195
                      case inl assump_197 =>
                        apply Or.inr
                        intro assump_203
                        have assump_804 : True := by
                          apply True.intro
                        let assump_211 := assump_185 assump_804
                        apply False.elim assump_211
                      case inr assump_198 =>
                        apply Or.inr
                        intro assump_219
                        have assump_805 : True := by
                          apply True.intro
                        let assump_227 := assump_185 assump_805
                        apply False.elim assump_227
            case inr assump_180 =>
              cases assump_6
              case intro assump_233 assump_234 =>
                cases assump_233
                case intro assump_235 assump_236 =>
                  cases assump_236
                  case intro assump_239 assump_240 =>
                    cases assump_234
                    case intro assump_245 assump_246 =>
                      cases assump_245
                      case inl assump_247 =>
                        apply Or.inr
                        intro assump_253
                        have assump_806 : True := by
                          apply True.intro
                        let assump_261 := assump_235 assump_806
                        apply False.elim assump_261
                      case inr assump_248 =>
                        apply Or.inr
                        intro assump_269
                        have assump_807 : True := by
                          apply True.intro
                        let assump_277 := assump_235 assump_807
                        apply False.elim assump_277
          case inr assump_178 =>
            cases assump_6
            case intro assump_283 assump_284 =>
              cases assump_283
              case intro assump_285 assump_286 =>
                cases assump_286
                case intro assump_289 assump_290 =>
                  cases assump_284
                  case intro assump_295 assump_296 =>
                    cases assump_295
                    case inl assump_297 =>
                      apply Or.inr
                      intro assump_303
                      have assump_808 : True := by
                        apply True.intro
                      let assump_311 := assump_285 assump_808
                      apply False.elim assump_311
                    case inr assump_298 =>
                      apply Or.inr
                      intro assump_319
                      have assump_809 : True := by
                        apply True.intro
                      let assump_327 := assump_285 assump_809
                      apply False.elim assump_327
  apply And.intro
  cases assump_1
  case intro assump_333 assump_334 =>
    cases assump_333
    case intro assump_335 assump_336 =>
      cases assump_335
      case inl assump_337 =>
        cases assump_337
        case intro assump_339 assump_340 =>
          cases assump_336
          case inl assump_345 =>
            cases assump_345
            case inl assump_347 =>
              cases assump_334
              case intro assump_351 assump_352 =>
                cases assump_351
                case intro assump_353 assump_354 =>
                  cases assump_354
                  case intro assump_357 assump_358 =>
                    cases assump_352
                    case intro assump_363 assump_364 =>
                      cases assump_363
                      case inl assump_365 =>
                        apply Or.inr
                        exact assump_339
                      case inr assump_366 =>
                        apply Or.inr
                        exact assump_339
            case inr assump_348 =>
              cases assump_334
              case intro assump_377 assump_378 =>
                cases assump_377
                case intro assump_379 assump_380 =>
                  cases assump_380
                  case intro assump_383 assump_384 =>
                    cases assump_378
                    case intro assump_389 assump_390 =>
                      cases assump_389
                      case inl assump_391 =>
                        apply Or.inr
                        exact assump_339
                      case inr assump_392 =>
                        apply Or.inr
                        exact assump_339
          case inr assump_346 =>
            cases assump_334
            case intro assump_403 assump_404 =>
              cases assump_403
              case intro assump_405 assump_406 =>
                cases assump_406
                case intro assump_409 assump_410 =>
                  cases assump_404
                  case intro assump_415 assump_416 =>
                    cases assump_415
                    case inl assump_417 =>
                      apply Or.inr
                      exact assump_339
                    case inr assump_418 =>
                      apply Or.inr
                      exact assump_339
      case inr assump_338 =>
        cases assump_338
        case intro assump_427 assump_428 =>
          cases assump_336
          case inl assump_433 =>
            cases assump_433
            case inl assump_435 =>
              cases assump_334
              case intro assump_439 assump_440 =>
                cases assump_439
                case intro assump_441 assump_442 =>
                  cases assump_442
                  case intro assump_445 assump_446 =>
                    cases assump_440
                    case intro assump_451 assump_452 =>
                      cases assump_451
                      case inl assump_453 =>
                        apply Or.inr
                        exact assump_427
                      case inr assump_454 =>
                        apply Or.inr
                        exact assump_427
            case inr assump_436 =>
              cases assump_334
              case intro assump_465 assump_466 =>
                cases assump_465
                case intro assump_467 assump_468 =>
                  cases assump_468
                  case intro assump_471 assump_472 =>
                    cases assump_466
                    case intro assump_477 assump_478 =>
                      cases assump_477
                      case inl assump_479 =>
                        apply Or.inr
                        exact assump_427
                      case inr assump_480 =>
                        apply Or.inr
                        exact assump_427
          case inr assump_434 =>
            cases assump_334
            case intro assump_491 assump_492 =>
              cases assump_491
              case intro assump_493 assump_494 =>
                cases assump_494
                case intro assump_497 assump_498 =>
                  cases assump_492
                  case intro assump_503 assump_504 =>
                    cases assump_503
                    case inl assump_505 =>
                      apply Or.inr
                      exact assump_427
                    case inr assump_506 =>
                      apply Or.inr
                      exact assump_427
  intro assump_515
  cases assump_1
  case intro assump_520 assump_521 =>
    cases assump_520
    case intro assump_522 assump_523 =>
      cases assump_522
      case inl assump_524 =>
        cases assump_524
        case intro assump_526 assump_527 =>
          cases assump_523
          case inl assump_532 =>
            cases assump_532
            case inl assump_534 =>
              cases assump_521
              case intro assump_538 assump_539 =>
                cases assump_538
                case intro assump_540 assump_541 =>
                  cases assump_541
                  case intro assump_544 assump_545 =>
                    cases assump_539
                    case intro assump_550 assump_551 =>
                      cases assump_550
                      case inl assump_552 =>
                        have assump_810 : True := by
                          apply True.intro
                        let assump_562 := assump_540 assump_810
                        apply False.elim assump_562
                      case inr assump_553 =>
                        have assump_811 : True := by
                          apply True.intro
                        let assump_574 := assump_540 assump_811
                        apply False.elim assump_574
            case inr assump_535 =>
              cases assump_521
              case intro assump_580 assump_581 =>
                cases assump_580
                case intro assump_582 assump_583 =>
                  cases assump_583
                  case intro assump_586 assump_587 =>
                    cases assump_581
                    case intro assump_592 assump_593 =>
                      cases assump_592
                      case inl assump_594 =>
                        have assump_812 : True := by
                          apply True.intro
                        let assump_604 := assump_582 assump_812
                        apply False.elim assump_604
                      case inr assump_595 =>
                        have assump_813 : True := by
                          apply True.intro
                        let assump_616 := assump_582 assump_813
                        apply False.elim assump_616
          case inr assump_533 =>
            cases assump_521
            case intro assump_622 assump_623 =>
              cases assump_622
              case intro assump_624 assump_625 =>
                cases assump_625
                case intro assump_628 assump_629 =>
                  cases assump_623
                  case intro assump_634 assump_635 =>
                    cases assump_634
                    case inl assump_636 =>
                      have assump_814 : True := by
                        apply True.intro
                      let assump_646 := assump_624 assump_814
                      apply False.elim assump_646
                    case inr assump_637 =>
                      have assump_815 : True := by
                        apply True.intro
                      let assump_658 := assump_624 assump_815
                      apply False.elim assump_658
      case inr assump_525 =>
        cases assump_525
        case intro assump_662 assump_663 =>
          cases assump_523
          case inl assump_668 =>
            cases assump_668
            case inl assump_670 =>
              cases assump_521
              case intro assump_674 assump_675 =>
                cases assump_674
                case intro assump_676 assump_677 =>
                  cases assump_677
                  case intro assump_680 assump_681 =>
                    cases assump_675
                    case intro assump_686 assump_687 =>
                      cases assump_686
                      case inl assump_688 =>
                        have assump_816 : True := by
                          apply True.intro
                        let assump_698 := assump_676 assump_816
                        apply False.elim assump_698
                      case inr assump_689 =>
                        have assump_817 : True := by
                          apply True.intro
                        let assump_710 := assump_676 assump_817
                        apply False.elim assump_710
            case inr assump_671 =>
              cases assump_521
              case intro assump_716 assump_717 =>
                cases assump_716
                case intro assump_718 assump_719 =>
                  cases assump_719
                  case intro assump_722 assump_723 =>
                    cases assump_717
                    case intro assump_728 assump_729 =>
                      cases assump_728
                      case inl assump_730 =>
                        have assump_818 : True := by
                          apply True.intro
                        let assump_740 := assump_718 assump_818
                        apply False.elim assump_740
                      case inr assump_731 =>
                        have assump_819 : True := by
                          apply True.intro
                        let assump_752 := assump_718 assump_819
                        apply False.elim assump_752
          case inr assump_669 =>
            cases assump_521
            case intro assump_758 assump_759 =>
              cases assump_758
              case intro assump_760 assump_761 =>
                cases assump_761
                case intro assump_764 assump_765 =>
                  cases assump_759
                  case intro assump_770 assump_771 =>
                    cases assump_770
                    case inl assump_772 =>
                      have assump_820 : True := by
                        apply True.intro
                      let assump_782 := assump_760 assump_820
                      apply False.elim assump_782
                    case inr assump_773 =>
                      have assump_821 : True := by
                        apply True.intro
                      let assump_794 := assump_760 assump_821
                      apply False.elim assump_794


variable (p0 p3 p5 p1 p4 p7 p6 p2 : Prop)
theorem file34_23740 : (((((p3 → False) ∧ (p2 ∨ p6)) ∨ ((p6 ∨ p3) → (True ∧ p5))) ∨ (((p0 → p3) ∨ (p2 → p1)) → False)) → ((((p4 → False) ∧ (True → False)) → False) ∨ (((p7 ∧ p3) → False) → ((p3 → False) ∨ (p3 ∨ p5))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          apply Or.inl
          intro assump_14
          cases assump_14
          case intro assump_15 assump_16 =>
            have assump_64 : True := by
              apply True.intro
            let assump_21 := assump_16 assump_64
            apply False.elim assump_21
        case inr assump_11 =>
          apply Or.inl
          intro assump_27
          cases assump_27
          case intro assump_28 assump_29 =>
            have assump_65 : True := by
              apply True.intro
            let assump_34 := assump_29 assump_65
            apply False.elim assump_34
    case inr assump_5 =>
      apply Or.inl
      intro assump_40
      cases assump_40
      case intro assump_41 assump_42 =>
        have assump_66 : True := by
          apply True.intro
        let assump_47 := assump_42 assump_66
        apply False.elim assump_47
  case inr assump_3 =>
    apply Or.inl
    intro assump_53
    cases assump_53
    case intro assump_54 assump_55 =>
      have assump_67 : True := by
        apply True.intro
      let assump_60 := assump_55 assump_67
      apply False.elim assump_60


variable (p4 p0 p1 p7 p3 p5 : Prop)
theorem file34_25325 : ((((((p3 → False) ∧ (p3 ∨ p5)) → ((p0 ∨ p4) ∨ (p0 → False))) → (((p4 → p7) → (p3 → p3)) ∨ ((p3 → p5) → (p0 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p3 → False) ∧ (p3 ∨ p5)) → ((p0 ∨ p4) ∨ (p0 → False))) → (((p4 → p7) → (p3 → p3)) ∨ ((p3 → p5) → (p0 ∧ p1)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    exact assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p0 p1 p5 : Prop)
theorem file34_25830 : ((((((p5 ∨ False) → (True → False)) ∧ ((p0 → p0) → False)) → (((True → p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p5 ∨ False) → (True → False)) ∧ ((p0 → p0) → False)) → (((True → p1) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_26 : (p0 → p0) := by
        intro assump_16
        exact assump_16
      let assump_15 := assump_10 assump_26
      apply False.elim assump_15
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p5 p6 p1 p3 p4 p7 p2 p0 : Prop)
theorem file34_26470 : (((((True → False) → (p4 ∧ p4)) → False) → (((p7 → p0) ∨ (p0 ∨ False)) → ((p5 ∨ p7) ∧ (p7 → p1)))) ∨ ((((p1 ∨ p4) ∧ (p4 → p4)) ∧ ((True ∨ p6) → False)) ∧ (((p3 → p2) ∧ (p6 ∧ p0)) ∧ ((True ∨ True) ∨ (p2 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    have assump_102 : ((True → False) → (p4 ∧ p4)) := by
      intro assump_10
      apply And.intro
      have assump_103 : True := by
        apply True.intro
      let assump_13 := assump_10 assump_103
      apply False.elim assump_13
      have assump_104 : True := by
        apply True.intro
      let assump_19 := assump_10 assump_104
      apply False.elim assump_19
    let assump_9 := assump_1 assump_102
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_26 =>
      have assump_105 : ((True → False) → (p4 ∧ p4)) := by
        intro assump_33
        apply And.intro
        have assump_106 : True := by
          apply True.intro
        let assump_36 := assump_33 assump_106
        apply False.elim assump_36
        have assump_107 : True := by
          apply True.intro
        let assump_42 := assump_33 assump_107
        apply False.elim assump_42
      let assump_32 := assump_1 assump_105
      apply False.elim assump_32
    case inr assump_27 =>
      apply False.elim assump_27
  intro assump_51
  cases assump_2
  case inl assump_54 =>
    have assump_108 : ((True → False) → (p4 ∧ p4)) := by
      intro assump_61
      apply And.intro
      have assump_109 : True := by
        apply True.intro
      let assump_64 := assump_61 assump_109
      apply False.elim assump_64
      have assump_110 : True := by
        apply True.intro
      let assump_70 := assump_61 assump_110
      apply False.elim assump_70
    let assump_60 := assump_1 assump_108
    apply False.elim assump_60
  case inr assump_55 =>
    cases assump_55
    case inl assump_77 =>
      have assump_111 : ((True → False) → (p4 ∧ p4)) := by
        intro assump_84
        apply And.intro
        have assump_112 : True := by
          apply True.intro
        let assump_87 := assump_84 assump_112
        apply False.elim assump_87
        have assump_113 : True := by
          apply True.intro
        let assump_93 := assump_84 assump_113
        apply False.elim assump_93
      let assump_83 := assump_1 assump_111
      apply False.elim assump_83
    case inr assump_78 =>
      apply False.elim assump_78


variable (p5 p7 p0 p3 p4 : Prop)
theorem file34_29005 : ((((((False → True) ∧ (True ∨ p5)) → ((p0 → False) ∨ (p7 ∧ p0))) → (((p3 ∧ False) ∨ (True ∨ p5)) ∧ ((False → False) ∨ (p0 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False → True) ∧ (True ∨ p5)) → ((p0 → False) ∨ (p7 ∧ p0))) → (((p3 ∧ False) ∨ (True ∨ p5)) ∧ ((False → False) ∨ (p0 ∨ p4)))) := by
    intro assump_5
    apply And.intro
    apply Or.inr
    apply Or.inl
    apply True.intro
    apply Or.inl
    intro assump_10
    apply False.elim assump_10
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p3 p7 p5 p1 p2 p4 : Prop)
theorem file34_29621 : (((((p6 ∨ True) → (p7 → False)) ∨ ((p7 → False) ∧ (p6 ∧ p1))) ∧ (((p7 → p2) → (p1 → False)) ∧ ((p5 ∨ p1) → (False ∧ True)))) → ((((p4 → False) ∧ (p5 → p3)) ∧ ((p5 ∧ p2) ∧ (p2 → p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_1
          case intro assump_21 assump_22 =>
            cases assump_21
            case inl assump_23 =>
              cases assump_22
              case intro assump_27 assump_28 =>
                have assump_59 : (p5 ∨ p1) := by
                  apply Or.inl
                  exact assump_13
                let assump_33 := assump_28 assump_59
                let assump_34 := And.left assump_33
                apply False.elim assump_34
            case inr assump_24 =>
              cases assump_24
              case intro assump_38 assump_39 =>
                cases assump_39
                case intro assump_42 assump_43 =>
                  cases assump_22
                  case intro assump_48 assump_49 =>
                    have assump_60 : (p5 ∨ p1) := by
                      apply Or.inl
                      exact assump_13
                    let assump_54 := assump_49 assump_60
                    let assump_55 := And.left assump_54
                    apply False.elim assump_55


variable (p4 p0 p2 p3 p5 p1 p7 p6 : Prop)
theorem file34_31190 : (((((p4 → p4) → False) ∧ ((p0 ∨ p1) ∧ (False → p0))) → (((p2 → False) ∨ (p3 ∨ p0)) → False)) ∨ ((((p4 ∧ False) → (p6 ∧ True)) → False) ∨ (((p5 ∧ p2) ∨ (p1 → False)) → ((p7 ∨ p5) ∧ (p7 ∨ p7))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case inl assump_7 =>
    cases assump_5
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          have assump_119 : (p4 → p4) := by
            intro assump_26
            exact assump_26
          let assump_25 := assump_11 assump_119
          apply False.elim assump_25
        case inr assump_18 =>
          have assump_120 : (p4 → p4) := by
            intro assump_39
            exact assump_39
          let assump_38 := assump_11 assump_120
          apply False.elim assump_38
  case inr assump_8 =>
    cases assump_8
    case inl assump_45 =>
      cases assump_5
      case intro assump_49 assump_50 =>
        cases assump_50
        case intro assump_53 assump_54 =>
          cases assump_53
          case inl assump_55 =>
            have assump_121 : (p4 → p4) := by
              intro assump_64
              exact assump_64
            let assump_63 := assump_49 assump_121
            apply False.elim assump_63
          case inr assump_56 =>
            have assump_122 : (p4 → p4) := by
              intro assump_77
              exact assump_77
            let assump_76 := assump_49 assump_122
            apply False.elim assump_76
    case inr assump_46 =>
      cases assump_5
      case intro assump_85 assump_86 =>
        cases assump_86
        case intro assump_89 assump_90 =>
          cases assump_89
          case inl assump_91 =>
            have assump_123 : (p4 → p4) := by
              intro assump_100
              exact assump_100
            let assump_99 := assump_85 assump_123
            apply False.elim assump_99
          case inr assump_92 =>
            have assump_124 : (p4 → p4) := by
              intro assump_113
              exact assump_113
            let assump_112 := assump_85 assump_124
            apply False.elim assump_112


variable (p7 p4 p3 p0 p1 p6 : Prop)
theorem file34_33426 : (((((p3 → False) → (p3 ∧ p4)) → False) ∧ (((p0 → p7) ∧ (False → False)) → False)) → ((((p3 → p3) → (p6 → True)) ∨ ((True → False) ∧ (p7 ∧ p1))) ∨ (((p1 → p1) → False) → ((False → False) ∧ (False ∧ True))))) := by
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    apply Or.inl
    apply Or.inl
    intro assump_30
    intro assump_31
    apply True.intro


variable (p0 p6 p7 p3 p2 : Prop)
theorem file34_33863 : (((((p7 ∨ p6) ∧ (p2 ∧ p3)) → ((False → False) ∧ (p0 → p2))) → False) → False) := by
  intro assump_1
  have assump_35 : (((p7 ∨ p6) ∧ (p2 ∧ p3)) → ((False → False) ∧ (p0 → p2))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_13
        case intro assump_18 assump_19 =>
          exact assump_18
      case inr assump_15 =>
        cases assump_13
        case intro assump_26 assump_27 =>
          exact assump_26
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p5 p3 p4 p6 p7 p0 : Prop)
theorem file34_34598 : (((((p4 → p4) → (True → False)) ∨ ((True → True) → False)) ∧ (((p3 → False) ∨ (False → False)) ∧ ((p5 ∨ p4) → (p0 → False)))) → ((((p6 → False) → False) → False) → (((p4 → False) ∨ (p6 ∧ p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            have assump_150 : (p4 → p4) := by
              intro assump_27
              exact assump_27
            let assump_26 := assump_12 assump_150
            have assump_151 : True := by
              apply True.intro
            let assump_30 := assump_26 assump_151
            apply False.elim assump_30
          case inr assump_19 =>
            have assump_152 : (p4 → p4) := by
              intro assump_41
              exact assump_41
            let assump_40 := assump_12 assump_152
            have assump_153 : True := by
              apply True.intro
            let assump_44 := assump_40 assump_153
            apply False.elim assump_44
      case inr assump_13 =>
        cases assump_11
        case intro assump_50 assump_51 =>
          cases assump_50
          case inl assump_52 =>
            have assump_154 : (True → True) := by
              intro assump_61
              apply True.intro
            let assump_60 := assump_13 assump_154
            apply False.elim assump_60
          case inr assump_53 =>
            have assump_155 : (True → True) := by
              intro assump_72
              apply True.intro
            let assump_71 := assump_13 assump_155
            apply False.elim assump_71
  case inr assump_5 =>
    cases assump_5
    case intro assump_76 assump_77 =>
      cases assump_1
      case intro assump_84 assump_85 =>
        cases assump_84
        case inl assump_86 =>
          cases assump_85
          case intro assump_90 assump_91 =>
            cases assump_90
            case inl assump_92 =>
              have assump_156 : (p4 → p4) := by
                intro assump_101
                exact assump_101
              let assump_100 := assump_86 assump_156
              have assump_157 : True := by
                apply True.intro
              let assump_104 := assump_100 assump_157
              apply False.elim assump_104
            case inr assump_93 =>
              have assump_158 : (p4 → p4) := by
                intro assump_115
                exact assump_115
              let assump_114 := assump_86 assump_158
              have assump_159 : True := by
                apply True.intro
              let assump_118 := assump_114 assump_159
              apply False.elim assump_118
        case inr assump_87 =>
          cases assump_85
          case intro assump_124 assump_125 =>
            cases assump_124
            case inl assump_126 =>
              have assump_160 : (True → True) := by
                intro assump_135
                apply True.intro
              let assump_134 := assump_87 assump_160
              apply False.elim assump_134
            case inr assump_127 =>
              have assump_161 : (True → True) := by
                intro assump_146
                apply True.intro
              let assump_145 := assump_87 assump_161
              apply False.elim assump_145


variable (p1 p0 p6 p2 p7 p5 p3 : Prop)
theorem file34_38108 : (((((p0 ∧ p5) → (p5 ∨ False)) ∨ ((p1 → True) ∨ (p1 → True))) ∧ (((p2 ∧ p1) → (p2 ∨ p2)) ∨ ((False ∨ p3) → False))) ∧ ((((p7 → False) ∨ (p5 → p6)) → ((p2 ∧ p6) → (p6 → True))) → (((False ∧ False) ∧ (False → False)) ∨ ((p5 ∧ p0) → (p0 ∨ p1))))) := by
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    exact assump_3
  apply Or.inl
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply Or.inl
    exact assump_9
  intro assump_15
  apply Or.inr
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    apply Or.inl
    exact assump_20


variable (p2 p5 p4 p1 p0 p3 p7 p6 : Prop)
theorem file34_38840 : ((((((p2 → False) → (p0 → p1)) → ((p2 ∧ p0) → (p5 → False))) → (((p0 ∧ p4) ∨ (p1 → False)) → False)) ∧ ((((p3 ∨ p3) ∨ (p4 ∨ p5)) ∧ ((p1 → p2) ∧ (p7 → p2))) ∧ (((p5 ∧ p1) ∨ (False → p6)) → False))) → False) := by
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
          case inl assump_12 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              have assump_84 : ((p5 ∧ p1) ∨ (False → p6)) := by
                apply Or.inr
                intro assump_25
                apply False.elim assump_25
              let assump_24 := assump_7 assump_84
              apply False.elim assump_24
          case inr assump_13 =>
            cases assump_9
            case intro assump_33 assump_34 =>
              have assump_85 : ((p5 ∧ p1) ∨ (False → p6)) := by
                apply Or.inr
                intro assump_42
                apply False.elim assump_42
              let assump_41 := assump_7 assump_85
              apply False.elim assump_41
        case inr assump_11 =>
          cases assump_11
          case inl assump_48 =>
            cases assump_9
            case intro assump_52 assump_53 =>
              have assump_86 : ((p5 ∧ p1) ∨ (False → p6)) := by
                apply Or.inr
                intro assump_61
                apply False.elim assump_61
              let assump_60 := assump_7 assump_86
              apply False.elim assump_60
          case inr assump_49 =>
            cases assump_9
            case intro assump_69 assump_70 =>
              have assump_87 : ((p5 ∧ p1) ∨ (False → p6)) := by
                apply Or.inr
                intro assump_78
                apply False.elim assump_78
              let assump_77 := assump_7 assump_87
              apply False.elim assump_77


variable (p3 p1 p5 p0 : Prop)
theorem file34_40879 : (((((p5 ∨ p0) ∧ (p1 ∨ False)) ∧ ((p1 → False) ∧ (p1 ∨ p3))) ∧ (((p0 → True) ∨ (p0 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case inl assump_12 =>
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_17
              case inl assump_20 =>
                have assump_74 : ((p0 → True) ∨ (p0 → True)) := by
                  apply Or.inl
                  intro assump_27
                  apply True.intro
                let assump_26 := assump_3 assump_74
                apply False.elim assump_26
              case inr assump_21 =>
                have assump_75 : ((p0 → True) ∨ (p0 → True)) := by
                  apply Or.inl
                  intro assump_36
                  apply True.intro
                let assump_35 := assump_3 assump_75
                apply False.elim assump_35
          case inr assump_13 =>
            apply False.elim assump_13
        case inr assump_9 =>
          cases assump_7
          case inl assump_44 =>
            cases assump_5
            case intro assump_48 assump_49 =>
              cases assump_49
              case inl assump_52 =>
                have assump_76 : ((p0 → True) ∨ (p0 → True)) := by
                  apply Or.inl
                  intro assump_59
                  apply True.intro
                let assump_58 := assump_3 assump_76
                apply False.elim assump_58
              case inr assump_53 =>
                have assump_77 : ((p0 → True) ∨ (p0 → True)) := by
                  apply Or.inl
                  intro assump_68
                  apply True.intro
                let assump_67 := assump_3 assump_77
                apply False.elim assump_67
          case inr assump_45 =>
            apply False.elim assump_45


variable (p0 p6 p2 p1 p7 p4 p3 p5 : Prop)
theorem file34_42978 : (((((p2 → p3) ∧ (True → False)) ∧ ((p2 → p2) ∨ (p2 → False))) ∧ (((True → p3) → (p0 ∧ p6)) ∨ ((p7 → False) ∧ (p4 → False)))) → ((((p7 ∨ p3) ∨ (p4 ∧ p1)) → ((True ∨ p4) ∨ (False ∧ p6))) ∨ (((p2 → p4) → (p3 ∨ p5)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          cases assump_3
          case inl assump_16 =>
            apply Or.inl
            intro assump_20
            cases assump_20
            case inl assump_21 =>
              cases assump_21
              case inl assump_23 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_24 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
            case inr assump_22 =>
              cases assump_22
              case intro assump_29 assump_30 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_17 =>
            cases assump_17
            case intro assump_35 assump_36 =>
              apply Or.inl
              intro assump_41
              cases assump_41
              case inl assump_42 =>
                cases assump_42
                case inl assump_44 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_45 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
              case inr assump_43 =>
                cases assump_43
                case intro assump_50 assump_51 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
        case inr assump_13 =>
          cases assump_3
          case inl assump_58 =>
            apply Or.inl
            intro assump_62
            cases assump_62
            case inl assump_63 =>
              cases assump_63
              case inl assump_65 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_66 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
            case inr assump_64 =>
              cases assump_64
              case intro assump_71 assump_72 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_59 =>
            cases assump_59
            case intro assump_77 assump_78 =>
              apply Or.inl
              intro assump_83
              cases assump_83
              case inl assump_84 =>
                cases assump_84
                case inl assump_86 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_87 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
              case inr assump_85 =>
                cases assump_85
                case intro assump_92 assump_93 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro


variable (p1 p3 p4 p2 p6 : Prop)
theorem file34_46339 : ((((((p6 → False) → (True ∨ p6)) ∨ ((p4 ∧ p4) ∨ (p2 → p1))) ∨ (((p1 → p3) ∧ (p3 → False)) ∨ ((p3 → False) ∧ (False ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 → False) → (True ∨ p6)) ∨ ((p4 ∧ p4) ∨ (p2 → p1))) ∨ (((p1 → p3) ∧ (p3 → False)) ∨ ((p3 → False) ∧ (False ∧ p4)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p1 p7 p5 p3 : Prop)
theorem file34_46864 : ((((((p1 ∨ p1) → (p1 → p3)) → ((p5 → False) ∧ (p0 ∨ True))) ∨ (((p1 → False) → False) ∧ ((p5 ∨ p7) → False))) ∧ ((((False → p5) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_46 : (((False → p5) → False) → False) := by
        intro assump_11
        have assump_47 : (False → p5) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_11 assump_47
        apply False.elim assump_14
      let assump_10 := assump_3 assump_46
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_24 assump_25 =>
        have assump_48 : (((False → p5) → False) → False) := by
          intro assump_33
          have assump_49 : (False → p5) := by
            intro assump_37
            apply False.elim assump_37
          let assump_36 := assump_33 assump_49
          apply False.elim assump_36
        let assump_32 := assump_3 assump_48
        apply False.elim assump_32


variable (p6 p7 p1 p4 p3 p0 p5 : Prop)
theorem file34_48010 : (((((p6 ∧ p5) → False) → False) → (((True ∧ False) → False) ∨ ((p6 → False) → False))) ∨ ((((p5 ∨ p7) ∨ (p0 → False)) ∨ ((p3 → p1) → False)) ∨ (((p5 → False) ∧ (p0 ∨ p4)) ∨ ((p4 ∨ False) ∨ (p5 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p5 p3 p7 p2 p6 p1 p0 p4 : Prop)
theorem file34_48433 : ((((((p6 → p5) ∧ (p0 ∧ p6)) ∧ ((p1 ∧ p2) ∧ (False ∧ p2))) ∧ (((True → p1) ∨ (p6 ∧ p2)) ∨ ((p7 ∨ p6) ∧ (p5 → p3)))) ∧ ((((True → False) ∨ (p7 ∨ p0)) ∧ ((p2 → p1) → (p6 ∨ p6))) → (((p4 → p3) → False) ∨ ((p6 ∧ True) ∨ (p3 ∨ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case intro assump_26 assump_27 =>
                  apply False.elim assump_26


variable (p2 p1 p6 p5 p7 : Prop)
theorem file34_49326 : ((((((p5 → p5) ∧ (p7 ∨ p6)) → ((False ∨ p6) ∧ (p7 → p2))) → (((p2 → False) ∨ (p1 ∧ p1)) → ((True ∨ p1) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p5 → p5) ∧ (p7 ∨ p6)) → ((False ∨ p6) ∧ (p7 → p2))) → (((p2 → False) ∨ (p1 ∧ p1)) → ((True ∨ p1) ∧ (False → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_13 assump_14 =>
        apply Or.inl
        apply True.intro
    intro assump_21
    apply False.elim assump_21
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p3 p6 p0 p4 p5 p2 p1 : Prop)
theorem file34_50093 : ((((((p4 → p3) ∨ (p3 ∧ p2)) ∧ ((p6 ∧ p4) ∨ (p3 ∧ True))) → (((p6 ∨ True) ∨ (p1 ∨ p2)) ∧ ((True → p0) ∧ (True ∨ p5)))) ∧ ((((p6 ∨ False) → False) ∧ ((False ∧ p5) ∧ (False ∧ p2))) ∧ (((False → False) → (p4 → p6)) → ((p1 ∨ True) → False)))) → False) := by
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
            apply False.elim assump_14


variable (p4 p5 p6 p0 p3 p1 : Prop)
theorem file34_50762 : ((((((p3 → False) ∨ (True → True)) → False) → (((p5 ∧ p3) → (p4 ∨ p5)) → False)) ∧ ((((p1 → p1) ∨ (True → p0)) → False) ∨ (((p1 → p1) ∨ (p6 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_26 : ((p1 → p1) ∨ (True → p0)) := by
        apply Or.inl
        intro assump_11
        exact assump_11
      let assump_10 := assump_6 assump_26
      apply False.elim assump_10
    case inr assump_7 =>
      have assump_27 : ((p1 → p1) ∨ (p6 → False)) := by
        apply Or.inl
        intro assump_20
        exact assump_20
      let assump_19 := assump_7 assump_27
      apply False.elim assump_19


variable (p5 p4 p7 p0 p3 p2 : Prop)
theorem file34_51534 : (((((p0 → False) ∧ (p0 → p3)) → ((p7 → p5) → False)) ∧ (((p2 ∧ p3) → (p4 ∧ p0)) ∧ ((p3 → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : (p3 → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_17
      apply False.elim assump_12


variable (p7 p1 : Prop)
theorem file34_51991 : ((((((p1 → False) → (p7 → p7)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p1 → False) → (p7 → p7)) → False) → False) := by
    intro assump_5
    have assump_22 : ((p1 → False) → (p7 → p7)) := by
      intro assump_9
      intro assump_10
      exact assump_10
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p3 p5 p2 p1 p6 p4 p0 : Prop)
theorem file34_52491 : (((((p3 ∨ p3) → (p1 → False)) → ((p7 → p6) ∧ (p2 → p7))) ∧ (((p4 ∧ p6) → (p1 ∨ True)) → False)) → ((((p5 → p1) ∧ (p3 ∨ p4)) → ((p6 → False) ∧ (p3 → p7))) ∨ (((p2 ∨ p0) → (p0 ∨ p7)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply And.intro
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        have assump_91 : ((p4 ∧ p6) → (p1 ∨ True)) := by
          intro assump_24
          cases assump_24
          case intro assump_25 assump_26 =>
            apply Or.inr
            apply True.intro
        let assump_23 := assump_3 assump_91
        apply False.elim assump_23
      case inr assump_17 =>
        have assump_92 : ((p4 ∧ p6) → (p1 ∨ True)) := by
          intro assump_40
          cases assump_40
          case intro assump_41 assump_42 =>
            apply Or.inr
            apply True.intro
        let assump_39 := assump_3 assump_92
        apply False.elim assump_39
    intro assump_50
    cases assump_8
    case intro assump_53 assump_54 =>
      cases assump_54
      case inl assump_57 =>
        have assump_93 : ((p4 ∧ p6) → (p1 ∨ True)) := by
          intro assump_65
          cases assump_65
          case intro assump_66 assump_67 =>
            apply Or.inr
            apply True.intro
        let assump_64 := assump_3 assump_93
        apply False.elim assump_64
      case inr assump_58 =>
        have assump_94 : ((p4 ∧ p6) → (p1 ∨ True)) := by
          intro assump_81
          cases assump_81
          case intro assump_82 assump_83 =>
            apply Or.inr
            apply True.intro
        let assump_80 := assump_3 assump_94
        apply False.elim assump_80


variable (p0 p7 p5 p6 p3 p4 p1 p2 : Prop)
theorem file34_54332 : (((((p6 ∧ p4) ∨ (p5 ∨ True)) → False) → False) ∨ ((((False → True) → (p7 → p1)) ∧ ((p7 ∧ False) → (p2 ∧ p1))) ∧ (((p7 ∨ p5) ∧ (p2 ∧ p2)) → ((p1 ∨ p0) ∧ (True ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p6 ∧ p4) ∨ (p5 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p2 p4 p5 p7 p0 : Prop)
theorem file34_54767 : (((((p0 → False) → (p4 → p4)) → ((p2 → p2) → False)) → False) ∨ ((((p2 → p5) → (p0 ∧ False)) ∨ ((p2 → False) → (p7 → p6))) → (((p5 → p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p0 → False) → (p4 → p4)) := by
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_18
  have assump_19 : (p2 → p2) := by
    intro assump_12
    exact assump_12
  let assump_11 := assump_4 assump_19
  apply False.elim assump_11


variable (p7 p3 p2 p6 p4 p5 : Prop)
theorem file34_55310 : (((((p5 ∨ p5) → (p2 ∧ True)) ∧ ((False → False) ∧ (False ∧ False))) ∧ (((p4 → False) → (p5 → False)) → False)) → ((((False ∧ True) ∧ (p5 → p5)) ∨ ((p4 ∧ p5) ∨ (p7 → False))) → (((p7 → False) ∨ (p6 → p6)) → ((p2 → p3) ∨ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
    case inr assump_9 =>
      cases assump_9
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_1
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              cases assump_27
              case intro assump_30 assump_31 =>
                cases assump_31
                case intro assump_34 assump_35 =>
                  apply False.elim assump_34
      case inr assump_17 =>
        cases assump_1
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            cases assump_43
            case intro assump_46 assump_47 =>
              cases assump_47
              case intro assump_50 assump_51 =>
                apply False.elim assump_50
  case inr assump_5 =>
    cases assump_2
    case inl assump_56 =>
      cases assump_56
      case intro assump_58 assump_59 =>
        cases assump_58
        case intro assump_60 assump_61 =>
          apply False.elim assump_60
    case inr assump_57 =>
      cases assump_57
      case inl assump_64 =>
        cases assump_64
        case intro assump_66 assump_67 =>
          cases assump_1
          case intro assump_72 assump_73 =>
            cases assump_72
            case intro assump_74 assump_75 =>
              cases assump_75
              case intro assump_78 assump_79 =>
                cases assump_79
                case intro assump_82 assump_83 =>
                  apply False.elim assump_82
      case inr assump_65 =>
        cases assump_1
        case intro assump_88 assump_89 =>
          cases assump_88
          case intro assump_90 assump_91 =>
            cases assump_91
            case intro assump_94 assump_95 =>
              cases assump_95
              case intro assump_98 assump_99 =>
                apply False.elim assump_98


variable (p3 p4 p2 p1 p7 : Prop)
theorem file34_57835 : (((((p1 ∧ p4) ∧ (p2 ∧ False)) ∧ ((p3 → False) ∧ (p7 → False))) ∧ (((p2 → p1) ∧ (p1 → p3)) ∨ ((p3 → p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            apply False.elim assump_15


variable (p7 p5 p0 p1 p3 p2 p6 p4 : Prop)
theorem file34_58383 : (((((True → p4) ∧ (p7 ∧ False)) ∧ ((p3 → False) → (False ∧ p0))) ∧ (((False ∨ p3) → False) ∧ ((True ∨ p3) → (p4 → p2)))) → ((((p2 ∨ p1) ∨ (p6 → p2)) → ((p1 ∨ p5) → (p4 ∧ p3))) ∨ (((False → False) → False) ∨ ((p2 ∧ p1) ∨ (p1 ∧ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_11


variable (p6 p5 p4 p0 p3 : Prop)
theorem file34_58964 : (((((p4 ∧ p6) ∧ (p0 ∧ p5)) → ((p5 → False) → (True ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_26 : (((p4 ∧ p6) ∧ (p0 ∧ p5)) → ((p5 → False) → (True ∨ p3))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p3 p4 p2 p5 : Prop)
theorem file34_59539 : ((((((p4 → False) ∧ (p4 → False)) → ((p5 ∧ p1) → (p2 ∨ p1))) → False) ∧ ((((p2 ∧ p4) ∧ (False ∨ True)) ∨ ((p3 ∨ False) ∧ (p5 → False))) ∧ (((p2 ∧ True) ∧ (p2 ∨ True)) ∨ ((p4 ∨ False) → (p3 ∧ False))))) → False) := by
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
            cases assump_11
            case inl assump_18 =>
              apply False.elim assump_18
            case inr assump_19 =>
              cases assump_7
              case inl assump_24 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_27
                    case inl assump_34 =>
                      have assump_183 : (((p4 → False) ∧ (p4 → False)) → ((p5 ∧ p1) → (p2 ∨ p1))) := by
                        intro assump_43
                        intro assump_44
                        cases assump_44
                        case intro assump_45 assump_46 =>
                          cases assump_43
                          case intro assump_51 assump_52 =>
                            apply Or.inl
                            exact assump_34
                      let assump_42 := assump_2 assump_183
                      apply False.elim assump_42
                    case inr assump_35 =>
                      have assump_184 : (((p4 → False) ∧ (p4 → False)) → ((p5 ∧ p1) → (p2 ∨ p1))) := by
                        intro assump_66
                        intro assump_67
                        cases assump_67
                        case intro assump_68 assump_69 =>
                          cases assump_66
                          case intro assump_74 assump_75 =>
                            apply Or.inl
                            exact assump_28
                      let assump_65 := assump_2 assump_184
                      apply False.elim assump_65
              case inr assump_25 =>
                have assump_185 : (p4 ∨ False) := by
                  apply Or.inl
                  exact assump_13
                let assump_85 := assump_25 assump_185
                let assump_86 := And.right assump_85
                apply False.elim assump_86
      case inr assump_9 =>
        cases assump_9
        case intro assump_91 assump_92 =>
          cases assump_91
          case inl assump_93 =>
            cases assump_7
            case inl assump_99 =>
              cases assump_99
              case intro assump_101 assump_102 =>
                cases assump_101
                case intro assump_103 assump_104 =>
                  cases assump_102
                  case inl assump_109 =>
                    have assump_186 : (((p4 → False) ∧ (p4 → False)) → ((p5 ∧ p1) → (p2 ∨ p1))) := by
                      intro assump_118
                      intro assump_119
                      cases assump_119
                      case intro assump_120 assump_121 =>
                        cases assump_118
                        case intro assump_126 assump_127 =>
                          apply Or.inl
                          exact assump_109
                    let assump_117 := assump_2 assump_186
                    apply False.elim assump_117
                  case inr assump_110 =>
                    have assump_187 : (((p4 → False) ∧ (p4 → False)) → ((p5 ∧ p1) → (p2 ∨ p1))) := by
                      intro assump_141
                      intro assump_142
                      cases assump_142
                      case intro assump_143 assump_144 =>
                        cases assump_141
                        case intro assump_149 assump_150 =>
                          apply Or.inl
                          exact assump_103
                    let assump_140 := assump_2 assump_187
                    apply False.elim assump_140
            case inr assump_100 =>
              have assump_188 : (((p4 → False) ∧ (p4 → False)) → ((p5 ∧ p1) → (p2 ∨ p1))) := by
                intro assump_164
                intro assump_165
                cases assump_165
                case intro assump_166 assump_167 =>
                  cases assump_164
                  case intro assump_172 assump_173 =>
                    apply Or.inr
                    exact assump_167
              let assump_163 := assump_2 assump_188
              apply False.elim assump_163
          case inr assump_94 =>
            apply False.elim assump_94


variable (p1 p2 p4 p6 p3 p5 p0 : Prop)
theorem file34_64304 : (((((True → False) ∧ (p4 → False)) → False) ∧ (((p5 → False) → (p0 ∨ False)) → ((True ∨ p2) → (False → False)))) ∨ ((((p6 ∨ p0) ∧ (p1 ∨ p0)) → False) → (((False → p0) ∨ (p0 → p0)) ∧ ((p3 ∨ p1) → False)))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : True := by
      apply True.intro
    let assump_9 := assump_2 assump_18
    apply False.elim assump_9
  intro assump_13
  intro assump_14
  intro assump_15
  apply False.elim assump_15


variable (p5 p7 p6 p1 p3 : Prop)
theorem file34_64880 : (((((p3 ∧ False) → False) → False) ∧ (((p3 ∨ p7) → (p6 → False)) ∧ ((p1 ∨ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_25 : ((p3 ∧ False) → False) := by
        intro assump_15
        cases assump_15
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
      let assump_14 := assump_2 assump_25
      apply False.elim assump_14


variable (p0 p6 p7 p5 p4 p2 : Prop)
theorem file34_65421 : (((((p0 → p7) → False) → ((False → p2) → (p4 → p2))) → False) → ((((p7 → p6) ∧ (p0 → p2)) → False) → (((p2 ∧ p5) ∨ (False ∨ p7)) → ((p7 ∨ p7) → (p7 → False))))) := by
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
        have assump_124 : (((p0 → p7) → False) → ((False → p2) → (p4 → p2))) := by
          intro assump_25
          intro assump_26
          intro assump_27
          exact assump_14
        let assump_24 := assump_1 assump_124
        apply False.elim assump_24
    case inr assump_13 =>
      cases assump_13
      case inl assump_37 =>
        apply False.elim assump_37
      case inr assump_38 =>
        have assump_125 : (((p0 → p7) → False) → ((False → p2) → (p4 → p2))) := by
          intro assump_48
          intro assump_49
          intro assump_50
          have assump_126 : (p0 → p7) := by
            intro assump_58
            exact assump_38
          let assump_57 := assump_48 assump_126
          apply False.elim assump_57
        let assump_47 := assump_1 assump_125
        apply False.elim assump_47
  case inr assump_9 =>
    cases assump_3
    case inl assump_69 =>
      cases assump_69
      case intro assump_71 assump_72 =>
        have assump_127 : (((p0 → p7) → False) → ((False → p2) → (p4 → p2))) := by
          intro assump_82
          intro assump_83
          intro assump_84
          exact assump_71
        let assump_81 := assump_1 assump_127
        apply False.elim assump_81
    case inr assump_70 =>
      cases assump_70
      case inl assump_94 =>
        apply False.elim assump_94
      case inr assump_95 =>
        have assump_128 : (((p0 → p7) → False) → ((False → p2) → (p4 → p2))) := by
          intro assump_105
          intro assump_106
          intro assump_107
          have assump_129 : (p0 → p7) := by
            intro assump_115
            exact assump_95
          let assump_114 := assump_105 assump_129
          apply False.elim assump_114
        let assump_104 := assump_1 assump_128
        apply False.elim assump_104


variable (p3 p4 p2 p0 p6 p7 p5 p1 : Prop)
theorem file34_67689 : (((((p7 ∧ p1) ∧ (p7 ∨ p4)) ∧ ((p6 → False) → (p5 → False))) → (((p0 ∧ p3) ∨ (p7 → p1)) → ((False ∧ p3) → False))) ∨ ((((p6 ∧ p2) → False) → ((p2 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_34
  intro assump_35
  intro assump_36
  cases assump_36
  case intro assump_37 assump_38 =>
    apply False.elim assump_37


variable (p0 p4 p2 p5 p1 p7 : Prop)
theorem file34_68083 : (((((p2 → False) ∧ (p2 ∧ True)) → False) ∧ (((p7 ∧ p1) ∨ (p5 ∧ p4)) ∨ ((p4 ∧ True) ∨ (True → p1)))) → ((((False ∧ p5) ∧ (p0 ∧ p7)) ∨ ((p0 → False) → (p1 ∧ True))) → (((False → True) ∨ (p4 → False)) ∨ ((True ∧ p7) → (p0 ∨ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
  case inr assump_4 =>
    cases assump_1
    case intro assump_13 assump_14 =>
      cases assump_14
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            apply Or.inl
            apply Or.inl
            intro assump_27
            apply True.intro
        case inr assump_20 =>
          cases assump_20
          case intro assump_28 assump_29 =>
            apply Or.inl
            apply Or.inl
            intro assump_34
            apply True.intro
      case inr assump_18 =>
        cases assump_18
        case inl assump_35 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            apply Or.inl
            apply Or.inl
            intro assump_43
            apply True.intro
        case inr assump_36 =>
          apply Or.inl
          apply Or.inl
          intro assump_46
          apply True.intro


variable (p5 p6 p4 p0 : Prop)
theorem file34_69553 : (((((True ∧ p5) → (p0 → False)) → ((True → True) ∨ (p6 → True))) → (((True ∧ p5) ∨ (False → p4)) → False)) → False) := by
  intro assump_1
  have assump_16 : (((True ∧ p5) → (p0 → False)) → ((True → True) ∨ (p6 → True))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_16
  have assump_17 : ((True ∧ p5) ∨ (False → p4)) := by
    apply Or.inr
    intro assump_10
    apply False.elim assump_10
  let assump_9 := assump_4 assump_17
  apply False.elim assump_9


variable (p0 p7 p4 p6 p1 p5 p3 : Prop)
theorem file34_70143 : (((((True → False) → (p5 → False)) ∧ ((p6 ∧ p1) ∧ (p1 → False))) ∧ (((False → True) → False) → ((p5 ∧ p3) → False))) ∨ ((((p4 ∨ p1) ∧ (True → False)) → False) ∧ (((True ∧ p4) → (p7 ∨ p0)) → ((p3 ∨ p1) → (p5 → p5))))) := by
  apply Or.inr
  apply And.intro
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      have assump_47 : True := by
        apply True.intro
      let assump_20 := assump_13 assump_47
      apply False.elim assump_20
    case inr assump_15 =>
      have assump_48 : True := by
        apply True.intro
      let assump_28 := assump_13 assump_48
      apply False.elim assump_28
  intro assump_32
  intro assump_33
  intro assump_34
  cases assump_33
  case inl assump_37 =>
    exact assump_34
  case inr assump_38 =>
    exact assump_34


variable (p0 p3 p6 : Prop)
theorem file34_71024 : (((((p0 ∨ p0) → False) → ((p6 → False) → (p3 → True))) → False) → False) := by
  intro assump_9
  have assump_19 : (((p0 ∨ p0) → False) → ((p6 → False) → (p3 → True))) := by
    intro assump_13
    intro assump_14
    intro assump_15
    apply True.intro
  let assump_12 := assump_9 assump_19
  apply False.elim assump_12


variable (p4 p0 p6 p7 p3 p2 : Prop)
theorem file34_71406 : ((((((p2 ∨ p7) ∧ (p6 → False)) ∨ ((p6 ∨ True) → (p4 ∨ True))) → False) ∧ ((((p2 ∧ True) → False) ∧ ((p7 ∨ p7) ∧ (p0 ∨ p6))) ∧ (((True → False) → (p3 ∨ False)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_17
            case inl assump_22 =>
              have assump_88 : ((True → False) → (p3 ∨ False)) := by
                intro assump_29
                have assump_89 : True := by
                  apply True.intro
                let assump_32 := assump_29 assump_89
                apply False.elim assump_32
              let assump_28 := assump_11 assump_88
              apply False.elim assump_28
            case inr assump_23 =>
              have assump_90 : ((True → False) → (p3 ∨ False)) := by
                intro assump_44
                have assump_91 : True := by
                  apply True.intro
                let assump_47 := assump_44 assump_91
                apply False.elim assump_47
              let assump_43 := assump_11 assump_90
              apply False.elim assump_43
          case inr assump_19 =>
            cases assump_17
            case inl assump_56 =>
              have assump_92 : ((True → False) → (p3 ∨ False)) := by
                intro assump_63
                have assump_93 : True := by
                  apply True.intro
                let assump_66 := assump_63 assump_93
                apply False.elim assump_66
              let assump_62 := assump_11 assump_92
              apply False.elim assump_62
            case inr assump_57 =>
              have assump_94 : ((True → False) → (p3 ∨ False)) := by
                intro assump_78
                have assump_95 : True := by
                  apply True.intro
                let assump_81 := assump_78 assump_95
                apply False.elim assump_81
              let assump_77 := assump_11 assump_94
              apply False.elim assump_77


variable (p2 p3 p6 p4 : Prop)
theorem file34_73652 : (((((True → False) ∧ (False → p3)) ∧ ((p3 → p6) ∨ (p4 → p2))) ∨ (((p2 ∨ p6) ∨ (p6 → False)) → False)) → False) := by
  intro assump_26
  cases assump_26
  case inl assump_27 =>
    cases assump_27
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_30
        case inl assump_37 =>
          have assump_69 : True := by
            apply True.intro
          let assump_43 := assump_31 assump_69
          apply False.elim assump_43
        case inr assump_38 =>
          have assump_70 : True := by
            apply True.intro
          let assump_51 := assump_31 assump_70
          apply False.elim assump_51
  case inr assump_28 =>
    have assump_71 : ((p2 ∨ p6) ∨ (p6 → False)) := by
      apply Or.inr
      intro assump_58
      have assump_72 : ((p2 ∨ p6) ∨ (p6 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_58
      let assump_62 := assump_28 assump_72
      apply False.elim assump_62
    let assump_57 := assump_28 assump_71
    apply False.elim assump_57


variable (p5 p1 p7 p2 p0 : Prop)
theorem file34_74781 : ((((((p5 → False) → False) ∨ ((p1 ∨ p2) → False)) → (((p5 ∧ p0) → (p1 ∨ p5)) ∨ ((p7 → p2) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p5 → False) → False) ∨ ((p1 ∨ p2) → False)) → (((p5 ∧ p0) → (p1 ∨ p5)) ∨ ((p7 → p2) → (p5 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply Or.inr
        exact assump_11
    case inr assump_7 =>
      apply Or.inl
      intro assump_19
      cases assump_19
      case intro assump_20 assump_21 =>
        apply Or.inr
        exact assump_20
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p5 p7 p0 p1 p3 p4 p6 : Prop)
theorem file34_75573 : (((((p3 ∧ p0) ∧ (p4 → False)) ∨ ((p1 → p6) → (False → False))) ∨ (((p7 → p7) ∧ (p1 ∨ p3)) ∨ ((False → p0) ∨ (p7 ∨ False)))) ∨ ((((p1 → False) → (p3 → p1)) ∧ ((p4 → False) → (p6 → False))) ∧ (((p4 → False) → False) → ((p5 ∧ p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p7 p3 p6 p4 p5 : Prop)
theorem file34_75982 : ((((((p3 → True) ∧ (p6 → p3)) → ((p4 → False) → (p7 → False))) → (((True → p5) ∧ (p6 ∧ p6)) → ((True ∧ True) ∨ (False ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p3 → True) ∧ (p6 → p3)) → ((p4 → False) → (p7 → False))) → (((True → p5) ∧ (p6 ∧ p6)) → ((True ∧ True) ∨ (False ∧ p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply And.intro
        apply True.intro
        apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p6 p5 p7 p1 p2 p4 : Prop)
theorem file34_76677 : ((((((True → p1) ∨ (True ∧ p7)) ∨ ((p4 → p6) ∧ (p6 ∧ p0))) → (((False ∧ p2) → (p4 ∧ p7)) ∨ ((p5 → True) ∧ (True ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_58 : ((((True → p1) ∨ (True ∧ p7)) ∨ ((p4 → p6) ∧ (p6 ∧ p0))) → (((False ∧ p2) → (p4 ∧ p7)) ∨ ((p5 → True) ∧ (True ∨ p7)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        apply And.intro
        cases assump_12
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
        cases assump_12
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
      case inr assump_9 =>
        cases assump_9
        case intro assump_21 assump_22 =>
          apply Or.inl
          intro assump_27
          apply And.intro
          cases assump_27
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
          cases assump_27
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
    case inr assump_7 =>
      cases assump_7
      case intro assump_36 assump_37 =>
        cases assump_37
        case intro assump_40 assump_41 =>
          apply Or.inl
          intro assump_46
          apply And.intro
          cases assump_46
          case intro assump_47 assump_48 =>
            apply False.elim assump_47
          cases assump_46
          case intro assump_51 assump_52 =>
            apply False.elim assump_51
  let assump_4 := assump_1 assump_58
  apply False.elim assump_4


variable (p3 p2 : Prop)
theorem file34_78312 : (((((False ∧ p3) → False) ∨ ((True → False) ∨ (p2 ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_13 : (((False ∧ p3) → False) ∨ ((True → False) ∨ (p2 ∨ p2))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p1 p2 p6 p3 p5 : Prop)
theorem file34_78737 : (((((p5 ∨ p3) ∨ (p5 → p2)) → False) ∧ (((p1 → False) ∧ (p5 ∧ p3)) ∨ ((p2 → p2) → (p6 → True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_49 : ((p5 ∨ p3) ∨ (p5 → p2)) := by
            apply Or.inl
            apply Or.inl
            exact assump_12
          let assump_21 := assump_2 assump_49
          apply False.elim assump_21
    case inr assump_7 =>
      have assump_50 : ((p5 ∨ p3) ∨ (p5 → p2)) := by
        apply Or.inr
        intro assump_33
        have assump_51 : ((p5 ∨ p3) ∨ (p5 → p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_33
        let assump_42 := assump_2 assump_51
        apply False.elim assump_42
      let assump_32 := assump_2 assump_50
      apply False.elim assump_32


variable (p1 p5 p0 p7 p2 : Prop)
theorem file34_79763 : ((((((p5 ∧ p1) ∨ (p0 → p0)) ∨ ((True → False) ∨ (p7 → False))) ∨ (((p1 ∧ p2) → False) ∧ ((False → True) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 ∧ p1) ∨ (p0 → p0)) ∨ ((True → False) ∨ (p7 → False))) ∨ (((p1 ∧ p2) → False) ∧ ((False → True) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p2 p0 p3 p6 p7 : Prop)
theorem file34_80271 : (((((p3 → p5) ∨ (p7 ∧ p3)) ∧ ((p2 → False) ∧ (p0 → p0))) ∧ (((False ∧ False) ∧ (p7 ∨ p0)) ∧ ((True ∨ p0) ∨ (p5 → p6)))) → ((((p7 ∨ p0) ∧ (p3 → False)) ∧ ((p5 ∧ p5) → False)) ∨ (((p6 → True) → False) → False))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          cases assump_7
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
      case inr assump_11 =>
        cases assump_11
        case intro assump_28 assump_29 =>
          cases assump_9
          case intro assump_34 assump_35 =>
            cases assump_7
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  apply False.elim assump_44


variable (p2 p5 p4 p1 p0 : Prop)
theorem file34_81486 : ((((((p0 ∨ p5) ∨ (p5 → False)) ∨ ((p4 ∨ p1) ∧ (True → False))) → (((p0 ∨ p1) ∨ (p0 ∨ True)) ∨ ((p0 → False) → (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p0 ∨ p5) ∨ (p5 → False)) ∨ ((p4 ∨ p1) ∧ (True → False))) → (((p0 ∨ p1) ∨ (p0 ∨ True)) ∨ ((p0 → False) → (p2 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_10
        case inr assump_11 =>
          apply Or.inl
          apply Or.inr
          apply Or.inr
          apply True.intro
      case inr assump_9 =>
        apply Or.inl
        apply Or.inr
        apply Or.inr
        apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_18 assump_19 =>
        cases assump_18
        case inl assump_20 =>
          apply Or.inl
          apply Or.inr
          apply Or.inr
          apply True.intro
        case inr assump_21 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_21
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p2 p4 p5 p0 p6 p1 : Prop)
theorem file34_82788 : (((((p4 → p5) ∧ (p5 ∧ False)) ∧ ((p0 ∧ p1) → False)) ∧ (((p0 ∨ False) ∨ (p5 ∧ p2)) → ((p2 → False) → False))) → ((((p6 ∧ True) → (p0 → p1)) ∧ ((p1 → p0) ∧ (p1 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_18
            case intro assump_21 assump_22 =>
              apply False.elim assump_22


variable (p1 p2 p7 p4 : Prop)
theorem file34_83480 : ((((((p1 → p1) ∨ (p4 → False)) → False) → (((p4 ∧ p7) → False) ∧ ((True ∧ p2) → (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p1 → p1) ∨ (p4 → False)) → False) → (((p4 ∧ p7) → False) ∧ ((True ∧ p2) → (p1 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_45 : ((p1 → p1) ∨ (p4 → False)) := by
        apply Or.inl
        intro assump_16
        exact assump_16
      let assump_15 := assump_5 assump_45
      apply False.elim assump_15
    intro assump_22
    intro assump_23
    cases assump_22
    case intro assump_26 assump_27 =>
      have assump_46 : ((p1 → p1) ∨ (p4 → False)) := by
        apply Or.inl
        intro assump_35
        exact assump_35
      let assump_34 := assump_5 assump_46
      apply False.elim assump_34
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p5 p7 p1 : Prop)
theorem file34_84463 : (((((p7 ∨ p5) ∨ (False → True)) → False) → False) ∨ ((((p1 ∨ p7) → (p7 → False)) → ((False → p1) → False)) → False)) := by
  apply Or.inl
  intro assump_15
  have assump_23 : ((p7 ∨ p5) ∨ (False → True)) := by
    apply Or.inr
    intro assump_19
    apply True.intro
  let assump_18 := assump_15 assump_23
  apply False.elim assump_18


variable (p4 p5 p2 p3 p6 p7 p0 : Prop)
theorem file34_84862 : (((((p0 ∧ p0) → False) → False) ∨ (((p3 → False) ∧ (True → p0)) ∨ ((p4 → False) → (p6 → False)))) → ((((p3 ∧ p4) ∨ (p0 ∨ p2)) → False) → (((p5 → False) → (True ∨ p3)) ∨ ((p2 → False) → (p7 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    apply Or.inl
    apply True.intro
  case inr assump_6 =>
    cases assump_6
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply Or.inl
        intro assump_20
        apply Or.inl
        apply True.intro
    case inr assump_13 =>
      apply Or.inl
      intro assump_25
      apply Or.inl
      apply True.intro


variable (p6 p5 p3 p0 p2 p7 p4 p1 : Prop)
theorem file34_85611 : ((((((p2 ∨ p1) ∨ (True → False)) → False) ∧ (((False → p7) ∧ (p7 → False)) → ((p6 ∨ p1) ∧ (False → False)))) ∧ ((((p3 ∧ p4) ∧ (True → False)) → ((True → p5) ∧ (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_51 : (((p3 ∧ p4) ∧ (True → False)) → ((True → p5) ∧ (p0 → False))) := by
        intro assump_13
        apply And.intro
        intro assump_14
        cases assump_13
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            have assump_52 : True := by
              apply True.intro
            let assump_27 := assump_18 assump_52
            apply False.elim assump_27
        intro assump_31
        cases assump_13
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            have assump_53 : True := by
              apply True.intro
            let assump_44 := assump_35 assump_53
            apply False.elim assump_44
      let assump_12 := assump_3 assump_51
      apply False.elim assump_12


variable (p7 p1 p0 p5 p3 p2 p6 p4 : Prop)
theorem file34_86851 : (((((True → False) ∧ (p1 ∧ p6)) ∧ ((p3 → p1) → (False → False))) → (((p6 → False) → False) → ((p0 ∧ p1) ∧ (p0 ∧ p1)))) ∨ ((((p5 → p2) ∧ (p6 ∧ p6)) → ((p4 → p2) ∧ (p0 ∨ p7))) ∨ (((p4 ∧ p6) ∧ (True → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_89 : True := by
          apply True.intro
        let assump_26 := assump_7 assump_89
        apply False.elim assump_26
  cases assump_1
  case intro assump_32 assump_33 =>
    cases assump_32
    case intro assump_34 assump_35 =>
      cases assump_35
      case intro assump_38 assump_39 =>
        exact assump_38
  apply And.intro
  cases assump_1
  case intro assump_48 assump_49 =>
    cases assump_48
    case intro assump_50 assump_51 =>
      cases assump_51
      case intro assump_54 assump_55 =>
        have assump_90 : True := by
          apply True.intro
        let assump_69 := assump_50 assump_90
        apply False.elim assump_69
  cases assump_1
  case intro assump_75 assump_76 =>
    cases assump_75
    case intro assump_77 assump_78 =>
      cases assump_78
      case intro assump_81 assump_82 =>
        exact assump_81


variable (p1 p6 p4 p0 p2 p3 : Prop)
theorem file34_88256 : (((((p4 ∨ True) ∨ (p3 → False)) ∧ ((p3 ∧ p3) ∨ (True ∧ p0))) → (((p3 → False) → (p4 ∨ True)) ∧ ((p2 ∧ p2) ∧ (p4 → False)))) → ((((False → p0) → False) → False) ∨ (((p1 → False) ∧ (p4 → False)) → ((p6 ∧ p3) → False)))) := by
  intro assump_7
  apply Or.inl
  intro assump_10
  have assump_20 : (False → p0) := by
    intro assump_14
    apply False.elim assump_14
  let assump_13 := assump_10 assump_20
  apply False.elim assump_13


variable (p6 p4 p7 p3 p1 p0 p5 : Prop)
theorem file34_88750 : (((((p4 → False) → False) → False) → (((p1 ∧ p7) → (False → False)) ∨ ((True ∨ p5) ∧ (False ∧ p6)))) ∨ ((((p4 → False) → False) ∧ ((p6 → False) ∨ (p0 → p7))) ∨ (((p0 ∨ False) ∨ (p3 → p5)) → False))) := by
  apply Or.inl
  intro assump_9
  apply Or.inl
  intro assump_12
  intro assump_13
  apply False.elim assump_13


variable (p5 p1 p2 p0 p4 p7 : Prop)
theorem file34_89127 : (((((p0 → True) → False) → False) ∨ (((p4 ∧ p7) → False) → ((True ∨ False) → (p5 ∨ True)))) ∧ ((((p2 ∨ True) ∨ (p7 ∨ p1)) → False) → False)) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_16 : (p0 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4
  intro assump_9
  have assump_17 : ((p2 ∨ True) ∨ (p7 ∨ p1)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_12 := assump_9 assump_17
  apply False.elim assump_12


variable (p0 p7 p4 p2 p6 p3 : Prop)
theorem file34_89716 : (((((p0 → p3) ∧ (False → False)) → False) ∧ (((p4 → True) → False) ∧ ((p4 ∨ False) → (p2 → p3)))) → ((((p7 → p7) ∧ (True → False)) → ((p7 → p7) ∨ (p6 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_21 : (p4 → True) := by
        intro assump_17
        apply True.intro
      let assump_16 := assump_9 assump_21
      apply False.elim assump_16


variable (p6 p3 p1 p0 : Prop)
theorem file34_90253 : ((((((p3 → p3) → False) ∧ ((p6 → False) ∧ (p1 ∧ p6))) → (((p0 ∨ True) ∨ (p3 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_80 : ((((p3 → p3) → False) ∧ ((p6 → False) ∧ (p1 ∧ p6))) → (((p0 ∨ True) ∨ (p3 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            cases assump_18
            case intro assump_21 assump_22 =>
              have assump_81 : p6 := by
                exact assump_22
              let assump_29 := assump_17 assump_81
              apply False.elim assump_29
      case inr assump_10 =>
        cases assump_5
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            cases assump_40
            case intro assump_43 assump_44 =>
              have assump_82 : p6 := by
                exact assump_44
              let assump_51 := assump_39 assump_82
              apply False.elim assump_51
    case inr assump_8 =>
      cases assump_5
      case intro assump_57 assump_58 =>
        cases assump_58
        case intro assump_61 assump_62 =>
          cases assump_62
          case intro assump_65 assump_66 =>
            have assump_83 : p6 := by
              exact assump_66
            let assump_73 := assump_61 assump_83
            apply False.elim assump_73
  let assump_4 := assump_1 assump_80
  apply False.elim assump_4


variable (p6 p3 p4 p0 p5 : Prop)
theorem file34_91913 : (((((p5 → True) ∨ (True ∧ p0)) ∧ ((p4 → p6) ∨ (p4 ∧ p3))) → False) → ((((p5 → p4) ∧ (p4 → False)) ∨ ((p5 ∨ p4) → (p6 → False))) → (((p4 ∧ p5) ∨ (p0 ∧ p4)) ∨ ((p0 ∧ False) ∨ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply Or.inr
      apply Or.inr
      intro assump_13
      have assump_41 : (((p5 → True) ∨ (True ∧ p0)) ∧ ((p4 → p6) ∨ (p4 ∧ p3))) := by
        apply And.intro
        apply Or.inl
        intro assump_18
        apply True.intro
        apply Or.inl
        intro assump_19
        exact assump_13
      let assump_17 := assump_1 assump_41
      apply False.elim assump_17
  case inr assump_4 =>
    apply Or.inr
    apply Or.inr
    intro assump_29
    have assump_42 : (((p5 → True) ∨ (True ∧ p0)) ∧ ((p4 → p6) ∨ (p4 ∧ p3))) := by
      apply And.intro
      apply Or.inl
      intro assump_34
      apply True.intro
      apply Or.inl
      intro assump_35
      exact assump_29
    let assump_33 := assump_1 assump_42
    apply False.elim assump_33


variable (p5 p2 p6 p3 p0 p4 p7 : Prop)
theorem file34_93064 : (((((p2 ∧ p5) ∨ (True ∧ False)) → ((p0 → True) → (p4 ∨ p5))) ∧ (((p6 → False) → (p6 → True)) ∨ ((p6 → False) → False))) ∨ ((((p3 → False) ∧ (p4 ∨ False)) ∧ ((p6 ∨ p7) → False)) ∨ (((p2 → p0) → False) ∨ ((p2 ∨ p2) ∧ (True ∧ True))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply Or.inr
      exact assump_8
  case inr assump_6 =>
    cases assump_6
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  apply Or.inl
  intro assump_19
  intro assump_20
  apply True.intro


variable (p7 p2 p6 p3 p5 p0 p1 p4 : Prop)
theorem file34_93754 : (((((p7 ∨ p6) ∧ (p5 → False)) → ((p0 → True) ∨ (p0 ∨ p2))) → False) → ((((False → p2) → False) ∨ ((p1 → False) ∧ (p3 → p5))) ∧ (((p0 → p5) ∨ (p4 ∧ p6)) ∨ ((p5 ∧ p2) ∨ (p2 → False))))) := by
  intro assump_5
  apply And.intro
  apply Or.inl
  intro assump_8
  have assump_56 : (((p7 ∨ p6) ∧ (p5 → False)) → ((p0 → True) ∨ (p0 ∨ p2))) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        apply Or.inl
        intro assump_22
        apply True.intro
      case inr assump_17 =>
        apply Or.inl
        intro assump_27
        apply True.intro
  let assump_12 := assump_5 assump_56
  apply False.elim assump_12
  apply Or.inl
  apply Or.inl
  intro assump_33
  have assump_57 : (((p7 ∨ p6) ∧ (p5 → False)) → ((p0 → True) ∨ (p0 ∨ p2))) := by
    intro assump_38
    cases assump_38
    case intro assump_39 assump_40 =>
      cases assump_39
      case inl assump_41 =>
        apply Or.inl
        intro assump_47
        apply True.intro
      case inr assump_42 =>
        apply Or.inl
        intro assump_52
        apply True.intro
  let assump_37 := assump_5 assump_57
  apply False.elim assump_37


variable (p0 p7 p2 p1 p4 p6 : Prop)
theorem file34_95009 : (((((p1 → False) → (False → False)) → False) → False) ∨ ((((p0 → False) → (p7 → p0)) → False) → (((p2 → False) → (p2 → False)) ∨ ((p6 ∧ p4) → (p2 → p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p1 → False) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p5 p3 p4 p2 p7 : Prop)
theorem file34_95454 : (((((True → False) → False) ∧ ((False ∧ p3) → False)) → False) → ((((p5 ∨ p4) → (p7 → False)) ∧ ((p5 → False) ∧ (p2 → False))) ∧ (((False ∨ p6) ∨ (p5 → False)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_137 : (((True → False) → False) ∧ ((False ∧ p3) → False)) := by
      apply And.intro
      intro assump_13
      have assump_138 : True := by
        apply True.intro
      let assump_16 := assump_13 assump_138
      apply False.elim assump_16
      intro assump_20
      cases assump_20
      case intro assump_21 assump_22 =>
        apply False.elim assump_21
    let assump_12 := assump_1 assump_137
    apply False.elim assump_12
  case inr assump_7 =>
    have assump_139 : (((True → False) → False) ∧ ((False ∧ p3) → False)) := by
      apply And.intro
      intro assump_33
      have assump_140 : True := by
        apply True.intro
      let assump_36 := assump_33 assump_140
      apply False.elim assump_36
      intro assump_40
      cases assump_40
      case intro assump_41 assump_42 =>
        apply False.elim assump_41
    let assump_32 := assump_1 assump_139
    apply False.elim assump_32
  apply And.intro
  intro assump_48
  have assump_141 : (((True → False) → False) ∧ ((False ∧ p3) → False)) := by
    apply And.intro
    intro assump_54
    have assump_142 : True := by
      apply True.intro
    let assump_57 := assump_54 assump_142
    apply False.elim assump_57
    intro assump_61
    cases assump_61
    case intro assump_62 assump_63 =>
      apply False.elim assump_62
  let assump_53 := assump_1 assump_141
  apply False.elim assump_53
  intro assump_69
  have assump_143 : (((True → False) → False) ∧ ((False ∧ p3) → False)) := by
    apply And.intro
    intro assump_75
    have assump_144 : True := by
      apply True.intro
    let assump_78 := assump_75 assump_144
    apply False.elim assump_78
    intro assump_82
    cases assump_82
    case intro assump_83 assump_84 =>
      apply False.elim assump_83
  let assump_74 := assump_1 assump_143
  apply False.elim assump_74
  intro assump_90
  cases assump_90
  case inl assump_91 =>
    cases assump_91
    case inl assump_93 =>
      apply False.elim assump_93
    case inr assump_94 =>
      have assump_145 : (((True → False) → False) ∧ ((False ∧ p3) → False)) := by
        apply And.intro
        intro assump_102
        have assump_146 : True := by
          apply True.intro
        let assump_105 := assump_102 assump_146
        apply False.elim assump_105
        intro assump_109
        cases assump_109
        case intro assump_110 assump_111 =>
          apply False.elim assump_110
      let assump_101 := assump_1 assump_145
      apply False.elim assump_101
  case inr assump_92 =>
    have assump_147 : (((True → False) → False) ∧ ((False ∧ p3) → False)) := by
      apply And.intro
      intro assump_122
      have assump_148 : True := by
        apply True.intro
      let assump_125 := assump_122 assump_148
      apply False.elim assump_125
      intro assump_129
      cases assump_129
      case intro assump_130 assump_131 =>
        apply False.elim assump_130
    let assump_121 := assump_1 assump_147
    apply False.elim assump_121


variable (p0 p2 p5 p7 p3 p4 : Prop)
theorem file34_98792 : ((((((p3 → p3) ∨ (p2 → p5)) → ((p0 → False) ∧ (False ∧ p4))) → (((p4 ∧ p0) ∧ (p3 → False)) ∧ ((p4 ∧ p4) → (p7 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_57 : ((((p3 → p3) ∨ (p2 → p5)) → ((p0 → False) ∧ (False ∧ p4))) → (((p4 ∧ p0) ∧ (p3 → False)) ∧ ((p4 ∧ p4) → (p7 ∨ p4)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    have assump_58 : ((p3 → p3) ∨ (p2 → p5)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_58
    let assump_12 := And.right assump_8
    let assump_14 := And.left assump_12
    apply False.elim assump_14
    have assump_59 : ((p3 → p3) ∨ (p2 → p5)) := by
      apply Or.inl
      intro assump_21
      exact assump_21
    let assump_20 := assump_5 assump_59
    let assump_24 := And.right assump_20
    let assump_26 := And.left assump_24
    apply False.elim assump_26
    intro assump_30
    have assump_60 : ((p3 → p3) ∨ (p2 → p5)) := by
      apply Or.inl
      intro assump_36
      exact assump_36
    let assump_35 := assump_5 assump_60
    let assump_39 := And.right assump_35
    let assump_41 := And.left assump_39
    apply False.elim assump_41
    intro assump_45
    cases assump_45
    case intro assump_46 assump_47 =>
      apply Or.inr
      exact assump_47
  let assump_4 := assump_1 assump_57
  apply False.elim assump_4


variable (p3 p5 p0 p2 p4 : Prop)
theorem file34_100228 : (((((False ∧ p3) → False) ∨ ((p5 → p4) → (p0 → False))) → False) → ((((p2 → False) → False) ∧ ((p5 ∧ False) → False)) ∧ (((p5 ∧ p3) → False) → False))) := by
  intro assump_26
  apply And.intro
  apply And.intro
  intro assump_27
  have assump_62 : (((False ∧ p3) → False) ∨ ((p5 → p4) → (p0 → False))) := by
    apply Or.inl
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      apply False.elim assump_34
  let assump_32 := assump_26 assump_62
  apply False.elim assump_32
  intro assump_41
  cases assump_41
  case intro assump_42 assump_43 =>
    apply False.elim assump_43
  intro assump_48
  have assump_63 : (((False ∧ p3) → False) ∨ ((p5 → p4) → (p0 → False))) := by
    apply Or.inl
    intro assump_54
    cases assump_54
    case intro assump_55 assump_56 =>
      apply False.elim assump_55
  let assump_53 := assump_26 assump_63
  apply False.elim assump_53


variable (p6 p2 p0 p4 p1 p5 p3 : Prop)
theorem file34_101192 : ((((((False ∨ p4) → (p0 ∧ True)) ∨ ((p2 ∧ p1) ∧ (p6 ∨ p2))) → (((p2 ∨ p2) → False) ∨ ((False ∧ p4) ∧ (p3 → False)))) ∧ ((((p5 ∧ p1) ∨ (p5 ∨ p6)) ∨ ((False ∧ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p5 ∧ p1) ∨ (p5 ∨ p6)) ∨ ((False ∧ p2) → False)) := by
      apply Or.inr
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p4 p1 p3 p6 p0 p2 : Prop)
theorem file34_101799 : (((((True → False) → False) ∨ ((p4 → False) → False)) → False) → ((((p0 ∧ p6) ∧ (p0 → False)) → ((p4 → p1) ∨ (p3 → False))) → (((True → False) ∨ (p0 → p2)) → False))) := by
  intro assump_10
  intro assump_11
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    have assump_49 : (((True → False) → False) ∨ ((p4 → False) → False)) := by
      apply Or.inl
      intro assump_22
      have assump_50 : True := by
        apply True.intro
      let assump_25 := assump_22 assump_50
      apply False.elim assump_25
    let assump_21 := assump_10 assump_49
    apply False.elim assump_21
  case inr assump_14 =>
    have assump_51 : (((True → False) → False) ∨ ((p4 → False) → False)) := by
      apply Or.inl
      intro assump_39
      have assump_52 : True := by
        apply True.intro
      let assump_42 := assump_39 assump_52
      apply False.elim assump_42
    let assump_38 := assump_10 assump_51
    apply False.elim assump_38


variable (p3 p1 p6 p7 p5 p0 p4 : Prop)
theorem file34_102809 : (((((p7 → p3) ∧ (p6 ∨ p1)) ∧ ((False ∧ p5) → False)) → False) → ((((p6 → p0) → False) → ((p0 → True) ∨ (p6 ∧ p5))) ∨ (((p5 → False) ∧ (p7 ∨ True)) ∧ ((p4 ∨ p3) → (True → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  apply True.intro


variable (p0 p4 p1 p6 p7 : Prop)
theorem file34_103153 : ((((((p0 → p7) → (True ∨ p6)) → False) → (((p1 ∧ p6) → False) ∧ ((p4 ∧ p1) ∧ (False ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p0 → p7) → (True ∨ p6)) → False) → (((p1 ∧ p6) → False) ∧ ((p4 ∧ p1) ∧ (False ∨ False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_53 : ((p0 → p7) → (True ∨ p6)) := by
        intro assump_16
        apply Or.inl
        apply True.intro
      let assump_15 := assump_5 assump_53
      apply False.elim assump_15
    apply And.intro
    apply And.intro
    have assump_54 : ((p0 → p7) → (True ∨ p6)) := by
      intro assump_25
      apply Or.inl
      apply True.intro
    let assump_24 := assump_5 assump_54
    apply False.elim assump_24
    have assump_55 : ((p0 → p7) → (True ∨ p6)) := by
      intro assump_34
      apply Or.inl
      apply True.intro
    let assump_33 := assump_5 assump_55
    apply False.elim assump_33
    have assump_56 : ((p0 → p7) → (True ∨ p6)) := by
      intro assump_43
      apply Or.inl
      apply True.intro
    let assump_42 := assump_5 assump_56
    apply False.elim assump_42
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p7 p3 p1 p0 p6 p4 p2 : Prop)
theorem file34_104454 : (((((p6 ∨ True) → False) → False) ∨ (((p4 ∧ p3) ∨ (p0 → False)) → False)) ∨ ((((p2 → False) → (p3 ∧ p7)) ∨ ((p1 → False) → (p0 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (p6 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p0 p4 p6 p3 p1 p5 : Prop)
theorem file34_104856 : (((((True ∨ p5) → (p6 → p0)) → ((p3 → False) ∧ (p4 ∧ p0))) → (((p1 → p2) ∧ (True ∧ p1)) → ((True → False) → (p1 ∨ p2)))) ∨ ((((p2 → p3) ∧ (False → False)) ∨ ((p2 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      apply Or.inl
      exact assump_11


variable (p7 p0 p1 p5 : Prop)
theorem file34_105322 : ((((((p0 ∧ p0) ∧ (False ∧ p5)) ∧ ((p1 ∧ False) ∧ (p1 ∨ True))) → (((p1 ∧ p7) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p0 ∧ p0) ∧ (False ∧ p5)) ∧ ((p1 ∧ False) ∧ (p1 ∨ True))) → (((p1 ∧ p7) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p3 p4 p6 p7 : Prop)
theorem file34_106027 : ((((((p7 ∧ True) → (True → False)) ∨ ((p3 → p4) → (p4 ∧ p4))) → (((True ∨ p3) ∧ (p6 ∨ p7)) → ((False → False) ∨ (p7 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_78 : ((((p7 ∧ True) → (True → False)) ∨ ((p3 → p4) → (p4 ∧ p4))) → (((True ∨ p3) ∧ (p6 ∨ p7)) → ((False → False) ∨ (p7 ∧ p4)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case inl assump_13 =>
          cases assump_5
          case inl assump_17 =>
            apply Or.inl
            intro assump_21
            apply False.elim assump_21
          case inr assump_18 =>
            apply Or.inl
            intro assump_26
            apply False.elim assump_26
        case inr assump_14 =>
          cases assump_5
          case inl assump_31 =>
            apply Or.inl
            intro assump_35
            apply False.elim assump_35
          case inr assump_32 =>
            apply Or.inl
            intro assump_40
            apply False.elim assump_40
      case inr assump_10 =>
        cases assump_8
        case inl assump_45 =>
          cases assump_5
          case inl assump_49 =>
            apply Or.inl
            intro assump_53
            apply False.elim assump_53
          case inr assump_50 =>
            apply Or.inl
            intro assump_58
            apply False.elim assump_58
        case inr assump_46 =>
          cases assump_5
          case inl assump_63 =>
            apply Or.inl
            intro assump_67
            apply False.elim assump_67
          case inr assump_64 =>
            apply Or.inl
            intro assump_72
            apply False.elim assump_72
  let assump_4 := assump_1 assump_78
  apply False.elim assump_4


variable (p1 p7 p4 p2 p0 p6 p3 : Prop)
theorem file34_107896 : ((((((p1 → False) → (p7 ∨ True)) ∧ ((p3 ∧ p0) → (p1 → False))) ∧ (((False → False) ∨ (p4 ∨ p4)) ∧ ((False ∧ p2) ∧ (p2 → False)))) ∧ ((((p6 ∨ p4) → (True → False)) ∨ ((p0 ∨ p7) ∨ (p3 → False))) ∨ (((p2 → p3) → (p2 → False)) → False))) → False) := by
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
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
          case inr assump_15 =>
            cases assump_15
            case inl assump_24 =>
              cases assump_13
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  apply False.elim assump_30
            case inr assump_25 =>
              cases assump_13
              case intro assump_36 assump_37 =>
                cases assump_36
                case intro assump_38 assump_39 =>
                  apply False.elim assump_38


variable (p6 p4 p1 p5 p2 p3 p7 : Prop)
theorem file34_109246 : (((((p7 → False) → False) → False) → (((True → False) → (p2 ∨ p1)) ∨ ((p4 → False) ∧ (p6 ∨ p1)))) → ((((False → p3) → (False → False)) → ((False → False) ∨ (p5 ∧ p4))) ∨ (((p4 ∧ False) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p1 p2 p5 p3 p4 p7 p0 p6 : Prop)
theorem file34_109632 : (((((p3 → False) → (p0 ∨ p3)) → ((p4 → False) ∨ (False → p5))) → (((False → p5) → False) ∨ ((p4 → p2) → False))) → ((((p7 → False) ∧ (p1 → False)) ∨ ((p3 ∧ False) → False)) → (((False → False) ∧ (p6 → False)) → ((False → False) ∨ (p6 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply Or.inl
        intro assump_20
        apply False.elim assump_20
    case inr assump_11 =>
      apply Or.inl
      intro assump_27
      apply False.elim assump_27


variable (p6 p0 p2 p5 : Prop)
theorem file34_110325 : ((((((p2 → p5) ∧ (True → False)) → False) ∨ (((p0 → True) → False) ∨ ((p6 → True) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p2 → p5) ∧ (True → False)) → False) ∨ (((p0 → True) → False) ∨ ((p6 → True) → (False → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p0 p1 p4 p2 p3 : Prop)
theorem file34_110945 : (((((True → False) → (p2 ∧ p6)) → ((False ∨ p2) → (p1 → False))) ∨ (((p0 → p6) ∨ (p3 → p3)) ∧ ((p4 ∨ p6) → False))) → ((((False ∧ True) → False) → ((p1 ∨ True) ∨ (p0 → False))) → (((True ∧ p6) ∨ (p2 → p2)) ∨ ((p4 ∧ p6) → (p6 → p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    apply Or.inr
    intro assump_9
    exact assump_9
  case inr assump_6 =>
    cases assump_6
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        apply Or.inl
        apply Or.inr
        intro assump_20
        exact assump_20
      case inr assump_15 =>
        apply Or.inl
        apply Or.inr
        intro assump_27
        exact assump_27


variable (p4 p6 p7 p0 p2 : Prop)
theorem file34_111727 : (((((p4 ∨ p2) ∨ (p4 → p7)) → False) → False) ∨ ((((p0 → False) → False) → ((p0 → False) → False)) ∨ (((p6 → False) → (p2 ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_33
  have assump_48 : ((p4 ∨ p2) ∨ (p4 → p7)) := by
    apply Or.inr
    intro assump_37
    have assump_49 : ((p4 ∨ p2) ∨ (p4 → p7)) := by
      apply Or.inl
      apply Or.inl
      exact assump_37
    let assump_41 := assump_33 assump_49
    apply False.elim assump_41
  let assump_36 := assump_33 assump_48
  apply False.elim assump_36


variable (p5 p4 p7 p3 p2 p1 p0 : Prop)
theorem file34_112305 : (((((p7 ∨ p5) → False) → ((p2 ∧ p5) → (p7 → p0))) → False) → ((((p2 ∨ p4) → (p7 → p1)) ∧ ((p0 ∧ p2) ∨ (p5 → p7))) → (((True → False) ∧ (p4 → False)) ∨ ((p2 → False) ∨ (p3 ∨ p1))))) := by
  intro assump_25
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_28
    case inl assump_31 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        apply Or.inl
        apply And.intro
        intro assump_41
        have assump_135 : (((p7 ∨ p5) → False) → ((p2 ∧ p5) → (p7 → p0))) := by
          intro assump_45
          intro assump_46
          intro assump_47
          cases assump_46
          case intro assump_50 assump_51 =>
            exact assump_33
        let assump_44 := assump_25 assump_135
        apply False.elim assump_44
        intro assump_61
        have assump_136 : (((p7 ∨ p5) → False) → ((p2 ∧ p5) → (p7 → p0))) := by
          intro assump_66
          intro assump_67
          intro assump_68
          cases assump_67
          case intro assump_71 assump_72 =>
            exact assump_33
        let assump_65 := assump_25 assump_136
        apply False.elim assump_65
    case inr assump_32 =>
      apply Or.inl
      apply And.intro
      intro assump_86
      have assump_137 : (((p7 ∨ p5) → False) → ((p2 ∧ p5) → (p7 → p0))) := by
        intro assump_90
        intro assump_91
        intro assump_92
        cases assump_91
        case intro assump_95 assump_96 =>
          have assump_138 : (p7 ∨ p5) := by
            apply Or.inl
            exact assump_92
          let assump_103 := assump_90 assump_138
          apply False.elim assump_103
      let assump_89 := assump_25 assump_137
      apply False.elim assump_89
      intro assump_110
      have assump_139 : (((p7 ∨ p5) → False) → ((p2 ∧ p5) → (p7 → p0))) := by
        intro assump_115
        intro assump_116
        intro assump_117
        cases assump_116
        case intro assump_120 assump_121 =>
          have assump_140 : (p7 ∨ p5) := by
            apply Or.inl
            exact assump_117
          let assump_128 := assump_115 assump_140
          apply False.elim assump_128
      let assump_114 := assump_25 assump_139
      apply False.elim assump_114


variable (p7 p4 p2 p3 p6 p5 p1 : Prop)
theorem file34_114596 : ((((((p4 ∧ p6) ∧ (False → False)) ∨ ((p7 ∨ True) → (p4 ∨ p3))) → False) ∧ ((((p7 → p2) → False) ∨ ((p7 ∨ p6) → (p1 ∨ True))) ∧ (((p3 ∨ p6) ∧ (p6 → False)) ∧ ((False → p5) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              have assump_78 : (False → p5) := by
                intro assump_25
                apply False.elim assump_25
              let assump_24 := assump_13 assump_78
              apply False.elim assump_24
            case inr assump_17 =>
              have assump_79 : (False → p5) := by
                intro assump_38
                apply False.elim assump_38
              let assump_37 := assump_13 assump_79
              apply False.elim assump_37
      case inr assump_9 =>
        cases assump_7
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_48
            case inl assump_50 =>
              have assump_80 : (False → p5) := by
                intro assump_59
                apply False.elim assump_59
              let assump_58 := assump_47 assump_80
              apply False.elim assump_58
            case inr assump_51 =>
              have assump_81 : (False → p5) := by
                intro assump_72
                apply False.elim assump_72
              let assump_71 := assump_47 assump_81
              apply False.elim assump_71


variable (p5 : Prop)
theorem file34_116367 : (((((False → p5) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p5) → False) → False) := by
    intro assump_5
    have assump_19 : (False → p5) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p3 p6 p2 p0 p4 p5 : Prop)
theorem file34_116810 : ((((((p5 → False) → (p0 → p5)) ∧ ((p5 → False) → False)) ∧ (((p2 ∧ False) ∧ (p5 ∨ p4)) → False)) ∧ ((((p4 ∧ False) ∧ (p6 ∨ p7)) ∨ ((p5 ∨ p3) ∨ (p4 ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_30 : (p5 → False) := by
          intro assump_19
          have assump_31 : (((p4 ∧ False) ∧ (p6 ∨ p7)) ∨ ((p5 ∨ p3) ∨ (p4 ∧ p6))) := by
            apply Or.inr
            apply Or.inl
            apply Or.inl
            exact assump_19
          let assump_23 := assump_3 assump_31
          apply False.elim assump_23
        let assump_18 := assump_7 assump_30
        apply False.elim assump_18


variable (p4 p7 p3 p6 p1 p5 p0 p2 : Prop)
theorem file34_117661 : ((((((p2 ∧ p7) ∧ (p5 → p5)) → ((True ∧ p3) ∧ (p0 ∧ True))) ∧ (((p3 → p7) ∧ (p4 ∨ False)) ∧ ((True ∧ False) ∧ (p7 ∨ p1)))) ∧ ((((p6 → False) ∧ (True → p6)) → ((p7 ∧ p2) → (True → False))) → (((p6 ∧ p6) ∧ (False → p7)) ∧ ((p0 → p4) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_21
          case inr assump_15 =>
            apply False.elim assump_15


variable (p2 p4 p7 p3 p1 p0 : Prop)
theorem file34_118548 : ((((((True ∧ p2) ∨ (p1 → False)) ∨ ((p0 ∨ p4) → False)) → False) ∧ ((((p0 ∨ p7) ∨ (p4 ∨ p3)) ∨ ((p3 ∧ p3) → False)) → False)) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    have assump_44 : (((p0 ∨ p7) ∨ (p4 ∨ p3)) ∨ ((p3 ∧ p3) → False)) := by
      apply Or.inr
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        have assump_45 : (((p0 ∨ p7) ∨ (p4 ∨ p3)) ∨ ((p3 ∧ p3) → False)) := by
          apply Or.inl
          apply Or.inr
          apply Or.inr
          exact assump_30
        let assump_37 := assump_22 assump_45
        apply False.elim assump_37
    let assump_27 := assump_22 assump_44
    apply False.elim assump_27


variable (p2 p6 p3 p0 p1 p7 : Prop)
theorem file34_119325 : (((((p6 ∧ p0) → (True ∨ p3)) ∨ ((True ∧ p2) ∨ (True ∨ p2))) → False) → ((((p3 ∨ p3) → False) ∧ ((True ∨ p2) ∧ (p2 ∧ p7))) ∨ (((True ∧ True) ∧ (False ∨ p7)) → ((p2 → p1) → False)))) := by
  intro assump_1
  apply Or.inr
  intro assump_35
  intro assump_36
  cases assump_35
  case intro assump_39 assump_40 =>
    cases assump_39
    case intro assump_41 assump_42 =>
      cases assump_40
      case inl assump_47 =>
        apply False.elim assump_47
      case inr assump_48 =>
        have assump_66 : (((p6 ∧ p0) → (True ∨ p3)) ∨ ((True ∧ p2) ∨ (True ∨ p2))) := by
          apply Or.inl
          intro assump_56
          cases assump_56
          case intro assump_57 assump_58 =>
            apply Or.inl
            apply True.intro
        let assump_55 := assump_1 assump_66
        apply False.elim assump_55


