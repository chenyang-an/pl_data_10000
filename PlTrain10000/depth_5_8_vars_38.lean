variable (p0 p2 p3 : Prop)
theorem file38_35 : (((((p2 → False) ∨ (p0 → False)) → ((True → False) → (p3 ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_28 : (((p2 → False) ∨ (p0 → False)) → ((True → False) → (p3 ∨ p2))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      have assump_29 : True := by
        apply True.intro
      let assump_14 := assump_6 assump_29
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_30 : True := by
        apply True.intro
      let assump_21 := assump_6 assump_30
      apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p6 p1 p4 p3 p2 p5 p0 p7 : Prop)
theorem file38_736 : (((((p7 → p2) ∧ (p4 ∧ False)) ∧ ((p5 ∨ p3) → (p7 ∧ p2))) → False) ∨ ((((p1 ∧ p2) ∨ (p5 → p7)) ∨ ((p6 ∧ p2) → (p5 ∨ p0))) → False)) := by
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_15


variable (p5 p3 p7 p4 p2 p0 p6 p1 : Prop)
theorem file38_1176 : (((((p0 → p4) ∨ (p6 ∨ p6)) → ((p7 ∧ p3) → (p7 ∧ True))) ∨ (((p2 ∨ False) ∧ (p6 ∨ p0)) ∨ ((p1 ∨ p1) → False))) → ((((p5 ∨ p3) ∧ (True → p1)) ∨ ((p1 ∨ p1) ∨ (False → p5))) ∧ (((p6 ∧ p0) → (p6 ∨ p0)) ∨ ((p7 ∧ p6) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    apply Or.inr
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            apply Or.inr
            apply Or.inr
            intro assump_21
            apply False.elim assump_21
          case inr assump_18 =>
            apply Or.inr
            apply Or.inr
            intro assump_26
            apply False.elim assump_26
        case inr assump_14 =>
          apply False.elim assump_14
    case inr assump_10 =>
      apply Or.inr
      apply Or.inr
      intro assump_33
      apply False.elim assump_33
  cases assump_1
  case inl assump_36 =>
    apply Or.inl
    intro assump_40
    cases assump_40
    case intro assump_41 assump_42 =>
      apply Or.inl
      exact assump_41
  case inr assump_37 =>
    cases assump_37
    case inl assump_47 =>
      cases assump_47
      case intro assump_49 assump_50 =>
        cases assump_49
        case inl assump_51 =>
          cases assump_50
          case inl assump_55 =>
            apply Or.inl
            intro assump_59
            cases assump_59
            case intro assump_60 assump_61 =>
              apply Or.inl
              exact assump_60
          case inr assump_56 =>
            apply Or.inl
            intro assump_68
            cases assump_68
            case intro assump_69 assump_70 =>
              apply Or.inl
              exact assump_69
        case inr assump_52 =>
          apply False.elim assump_52
    case inr assump_48 =>
      apply Or.inl
      intro assump_79
      cases assump_79
      case intro assump_80 assump_81 =>
        apply Or.inl
        exact assump_80


variable (p0 p5 : Prop)
theorem file38_3364 : (((((p0 → p5) → False) ∧ ((False → False) ∧ (False → False))) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_27 : ((True → False) → False) := by
          intro assump_17
          have assump_28 : True := by
            apply True.intro
          let assump_20 := assump_17 assump_28
          apply False.elim assump_20
        let assump_16 := assump_3 assump_27
        apply False.elim assump_16


variable (p2 p1 p7 p5 p0 p4 p3 : Prop)
theorem file38_4036 : (((((p5 ∨ p2) ∧ (p3 ∧ p2)) ∧ ((True ∨ p7) ∨ (p2 → p7))) ∧ (((p2 ∧ p0) ∧ (p2 → False)) ∧ ((True → p3) → (p1 → p1)))) → ((((p1 → p5) → (True ∧ p2)) ∧ ((p1 → False) → False)) ∧ (((p7 ∧ p5) → (p4 ∨ p5)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_10
          case intro assump_15 assump_16 =>
            cases assump_8
            case inl assump_21 =>
              cases assump_21
              case inl assump_23 =>
                cases assump_6
                case intro assump_27 assump_28 =>
                  cases assump_27
                  case intro assump_29 assump_30 =>
                    cases assump_29
                    case intro assump_31 assump_32 =>
                      exact assump_31
              case inr assump_24 =>
                cases assump_6
                case intro assump_43 assump_44 =>
                  cases assump_43
                  case intro assump_45 assump_46 =>
                    cases assump_45
                    case intro assump_47 assump_48 =>
                      exact assump_47
            case inr assump_22 =>
              cases assump_6
              case intro assump_59 assump_60 =>
                cases assump_59
                case intro assump_61 assump_62 =>
                  cases assump_61
                  case intro assump_63 assump_64 =>
                    exact assump_63
        case inr assump_12 =>
          cases assump_10
          case intro assump_75 assump_76 =>
            cases assump_8
            case inl assump_81 =>
              cases assump_81
              case inl assump_83 =>
                cases assump_6
                case intro assump_87 assump_88 =>
                  cases assump_87
                  case intro assump_89 assump_90 =>
                    cases assump_89
                    case intro assump_91 assump_92 =>
                      exact assump_91
              case inr assump_84 =>
                cases assump_6
                case intro assump_103 assump_104 =>
                  cases assump_103
                  case intro assump_105 assump_106 =>
                    cases assump_105
                    case intro assump_107 assump_108 =>
                      exact assump_107
            case inr assump_82 =>
              cases assump_6
              case intro assump_119 assump_120 =>
                cases assump_119
                case intro assump_121 assump_122 =>
                  cases assump_121
                  case intro assump_123 assump_124 =>
                    exact assump_123
  intro assump_133
  cases assump_1
  case intro assump_136 assump_137 =>
    cases assump_136
    case intro assump_138 assump_139 =>
      cases assump_138
      case intro assump_140 assump_141 =>
        cases assump_140
        case inl assump_142 =>
          cases assump_141
          case intro assump_146 assump_147 =>
            cases assump_139
            case inl assump_152 =>
              cases assump_152
              case inl assump_154 =>
                cases assump_137
                case intro assump_158 assump_159 =>
                  cases assump_158
                  case intro assump_160 assump_161 =>
                    cases assump_160
                    case intro assump_162 assump_163 =>
                      have assump_503 : p2 := by
                        exact assump_162
                      let assump_177 := assump_161 assump_503
                      apply False.elim assump_177
              case inr assump_155 =>
                cases assump_137
                case intro assump_183 assump_184 =>
                  cases assump_183
                  case intro assump_185 assump_186 =>
                    cases assump_185
                    case intro assump_187 assump_188 =>
                      have assump_504 : p2 := by
                        exact assump_187
                      let assump_202 := assump_186 assump_504
                      apply False.elim assump_202
            case inr assump_153 =>
              cases assump_137
              case intro assump_208 assump_209 =>
                cases assump_208
                case intro assump_210 assump_211 =>
                  cases assump_210
                  case intro assump_212 assump_213 =>
                    have assump_505 : p2 := by
                      exact assump_212
                    let assump_227 := assump_211 assump_505
                    apply False.elim assump_227
        case inr assump_143 =>
          cases assump_141
          case intro assump_233 assump_234 =>
            cases assump_139
            case inl assump_239 =>
              cases assump_239
              case inl assump_241 =>
                cases assump_137
                case intro assump_245 assump_246 =>
                  cases assump_245
                  case intro assump_247 assump_248 =>
                    cases assump_247
                    case intro assump_249 assump_250 =>
                      have assump_506 : p2 := by
                        exact assump_249
                      let assump_264 := assump_248 assump_506
                      apply False.elim assump_264
              case inr assump_242 =>
                cases assump_137
                case intro assump_270 assump_271 =>
                  cases assump_270
                  case intro assump_272 assump_273 =>
                    cases assump_272
                    case intro assump_274 assump_275 =>
                      have assump_507 : p2 := by
                        exact assump_274
                      let assump_289 := assump_273 assump_507
                      apply False.elim assump_289
            case inr assump_240 =>
              cases assump_137
              case intro assump_295 assump_296 =>
                cases assump_295
                case intro assump_297 assump_298 =>
                  cases assump_297
                  case intro assump_299 assump_300 =>
                    have assump_508 : p2 := by
                      exact assump_299
                    let assump_314 := assump_298 assump_508
                    apply False.elim assump_314
  intro assump_318
  cases assump_1
  case intro assump_321 assump_322 =>
    cases assump_321
    case intro assump_323 assump_324 =>
      cases assump_323
      case intro assump_325 assump_326 =>
        cases assump_325
        case inl assump_327 =>
          cases assump_326
          case intro assump_331 assump_332 =>
            cases assump_324
            case inl assump_337 =>
              cases assump_337
              case inl assump_339 =>
                cases assump_322
                case intro assump_343 assump_344 =>
                  cases assump_343
                  case intro assump_345 assump_346 =>
                    cases assump_345
                    case intro assump_347 assump_348 =>
                      have assump_509 : p2 := by
                        exact assump_347
                      let assump_362 := assump_346 assump_509
                      apply False.elim assump_362
              case inr assump_340 =>
                cases assump_322
                case intro assump_368 assump_369 =>
                  cases assump_368
                  case intro assump_370 assump_371 =>
                    cases assump_370
                    case intro assump_372 assump_373 =>
                      have assump_510 : p2 := by
                        exact assump_372
                      let assump_387 := assump_371 assump_510
                      apply False.elim assump_387
            case inr assump_338 =>
              cases assump_322
              case intro assump_393 assump_394 =>
                cases assump_393
                case intro assump_395 assump_396 =>
                  cases assump_395
                  case intro assump_397 assump_398 =>
                    have assump_511 : p2 := by
                      exact assump_397
                    let assump_412 := assump_396 assump_511
                    apply False.elim assump_412
        case inr assump_328 =>
          cases assump_326
          case intro assump_418 assump_419 =>
            cases assump_324
            case inl assump_424 =>
              cases assump_424
              case inl assump_426 =>
                cases assump_322
                case intro assump_430 assump_431 =>
                  cases assump_430
                  case intro assump_432 assump_433 =>
                    cases assump_432
                    case intro assump_434 assump_435 =>
                      have assump_512 : p2 := by
                        exact assump_434
                      let assump_449 := assump_433 assump_512
                      apply False.elim assump_449
              case inr assump_427 =>
                cases assump_322
                case intro assump_455 assump_456 =>
                  cases assump_455
                  case intro assump_457 assump_458 =>
                    cases assump_457
                    case intro assump_459 assump_460 =>
                      have assump_513 : p2 := by
                        exact assump_459
                      let assump_474 := assump_458 assump_513
                      apply False.elim assump_474
            case inr assump_425 =>
              cases assump_322
              case intro assump_480 assump_481 =>
                cases assump_480
                case intro assump_482 assump_483 =>
                  cases assump_482
                  case intro assump_484 assump_485 =>
                    have assump_514 : p2 := by
                      exact assump_484
                    let assump_499 := assump_483 assump_514
                    apply False.elim assump_499


variable (p5 p3 p7 p0 p1 p2 p6 : Prop)
theorem file38_14195 : ((((((p2 ∧ p5) ∨ (p1 → p2)) → ((p0 ∧ p0) → (p7 ∨ p3))) ∨ (((p5 → p6) → False) → False)) ∧ ((((p3 → True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_38 : (((p3 → True) → False) → False) := by
        intro assump_11
        have assump_39 : (p3 → True) := by
          intro assump_15
          apply True.intro
        let assump_14 := assump_11 assump_39
        apply False.elim assump_14
      let assump_10 := assump_3 assump_38
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_40 : (((p3 → True) → False) → False) := by
        intro assump_27
        have assump_41 : (p3 → True) := by
          intro assump_31
          apply True.intro
        let assump_30 := assump_27 assump_41
        apply False.elim assump_30
      let assump_26 := assump_3 assump_40
      apply False.elim assump_26


variable (p6 p3 p7 p1 p0 p5 : Prop)
theorem file38_15212 : (((((False ∧ p3) → (p5 ∨ p3)) → False) → (((True ∧ p6) → (p1 ∨ p1)) → ((True → False) → (p0 → False)))) ∨ ((((p7 → False) → (p5 → p0)) → ((p5 ∧ p5) → False)) ∧ (((p7 → False) → False) → ((p6 ∧ p3) ∨ (True → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  have assump_22 : ((False ∧ p3) → (p5 ∨ p3)) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_15
  let assump_13 := assump_1 assump_22
  apply False.elim assump_13


variable (p6 p5 p4 p7 p0 : Prop)
theorem file38_15806 : (((((True → False) → False) ∨ ((p5 → False) → False)) ∧ (((True → p0) → False) → ((p0 ∧ p6) ∨ (p0 → False)))) ∨ ((((p6 ∨ p6) ∨ (p0 ∧ p4)) ∨ ((False → False) ∧ (p7 ∨ p5))) → False)) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_22 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4
  intro assump_8
  apply Or.inr
  intro assump_11
  have assump_23 : (True → p0) := by
    intro assump_16
    exact assump_11
  let assump_15 := assump_8 assump_23
  apply False.elim assump_15


variable (p5 p6 p4 p1 p2 p0 p3 : Prop)
theorem file38_16431 : (((((p3 ∨ p1) ∨ (p6 ∧ False)) ∨ ((False → False) → (True ∨ p0))) → (((p0 ∧ p1) → (p2 ∧ p4)) ∧ ((False → p6) → False))) → ((((p6 → p0) ∨ (True ∧ p4)) → ((p6 → False) ∨ (p1 → p3))) → (((False ∧ p6) → False) ∨ ((True → False) ∨ (p5 → False))))) := by
  intro assump_19
  intro assump_20
  apply Or.inl
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    apply False.elim assump_26


variable (p6 p5 p7 p1 p3 : Prop)
theorem file38_16890 : (((((p1 ∧ False) ∧ (p7 → False)) → ((p3 ∨ p5) ∨ (p6 ∧ p1))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p1 ∧ False) ∧ (p7 → False)) → ((p3 ∨ p5) ∨ (p6 ∧ p1))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p3 p4 p7 : Prop)
theorem file38_17360 : ((((((False ∧ p7) → False) → False) ∧ (((p5 → False) ∨ (p4 ∨ p3)) ∨ ((True → False) → False))) ∧ ((((p3 ∧ True) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_106 : (((p3 ∧ True) ∧ (True → False)) → False) := by
            intro assump_17
            cases assump_17
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_107 : True := by
                  apply True.intro
                let assump_28 := assump_19 assump_107
                apply False.elim assump_28
          let assump_16 := assump_3 assump_106
          apply False.elim assump_16
        case inr assump_11 =>
          cases assump_11
          case inl assump_35 =>
            have assump_108 : (((p3 ∧ True) ∧ (True → False)) → False) := by
              intro assump_42
              cases assump_42
              case intro assump_43 assump_44 =>
                cases assump_43
                case intro assump_45 assump_46 =>
                  have assump_109 : True := by
                    apply True.intro
                  let assump_53 := assump_44 assump_109
                  apply False.elim assump_53
            let assump_41 := assump_3 assump_108
            apply False.elim assump_41
          case inr assump_36 =>
            have assump_110 : (((p3 ∧ True) ∧ (True → False)) → False) := by
              intro assump_65
              cases assump_65
              case intro assump_66 assump_67 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  have assump_111 : True := by
                    apply True.intro
                  let assump_76 := assump_67 assump_111
                  apply False.elim assump_76
            let assump_64 := assump_3 assump_110
            apply False.elim assump_64
      case inr assump_9 =>
        have assump_112 : (((p3 ∧ True) ∧ (True → False)) → False) := by
          intro assump_88
          cases assump_88
          case intro assump_89 assump_90 =>
            cases assump_89
            case intro assump_91 assump_92 =>
              have assump_113 : True := by
                apply True.intro
              let assump_99 := assump_90 assump_113
              apply False.elim assump_99
        let assump_87 := assump_3 assump_112
        apply False.elim assump_87


variable (p0 p5 p3 p2 p1 : Prop)
theorem file38_20040 : ((((((p2 ∨ p5) ∨ (p1 ∨ True)) → False) → (((False ∧ p3) → (p5 ∨ p0)) → ((p1 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p2 ∨ p5) ∨ (p1 ∨ True)) → False) → (((False ∧ p3) → (p5 ∨ p0)) → ((p1 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_22 : ((p2 ∨ p5) ∨ (p1 ∨ True)) := by
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_14 := assump_5 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p7 p4 p6 p2 p1 : Prop)
theorem file38_20663 : (((((True ∨ p7) ∨ (p0 ∧ True)) → ((p4 ∧ False) ∨ (p4 ∧ False))) → False) ∨ ((((p2 → p2) ∨ (p7 → p6)) → ((p4 → False) ∧ (True → False))) → (((p6 ∨ p1) ∨ (p1 → False)) ∧ ((p0 ∧ p4) ∨ (p1 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_20 : ((True ∨ p7) ∨ (p0 ∧ True)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_20
  cases assump_4
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  case inr assump_7 =>
    cases assump_7
    case intro assump_14 assump_15 =>
      apply False.elim assump_15


variable (p2 p4 p1 p7 p5 p0 : Prop)
theorem file38_21341 : (((((False → p0) ∧ (p2 → p2)) ∨ ((True → False) ∧ (p5 ∧ p4))) → False) → ((((p0 ∨ p7) ∨ (p7 → False)) ∧ ((p1 → False) → False)) → (((p4 ∧ p0) → False) → ((p5 → False) → (p0 → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply True.intro


variable (p7 p4 p2 p3 : Prop)
theorem file38_21690 : ((((((p4 → False) → (p7 ∨ p7)) → False) → (((p7 ∧ p3) → False) ∨ ((p2 → True) → False))) → False) → False) := by
  intro assump_5
  have assump_31 : ((((p4 → False) → (p7 ∨ p7)) → False) → (((p7 ∧ p3) → False) ∨ ((p2 → True) → False))) := by
    intro assump_9
    apply Or.inl
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      have assump_32 : ((p4 → False) → (p7 ∨ p7)) := by
        intro assump_22
        apply Or.inl
        exact assump_13
      let assump_21 := assump_9 assump_32
      apply False.elim assump_21
  let assump_8 := assump_5 assump_31
  apply False.elim assump_8


variable (p7 p4 : Prop)
theorem file38_22359 : (((((p4 → False) → (False → p7)) ∨ ((False ∨ p7) → (True → False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p4 → False) → (False → p7)) ∨ ((False ∨ p7) → (True → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p3 p0 p5 p2 p7 : Prop)
theorem file38_22769 : (((((p4 ∨ p5) ∧ (p0 ∧ True)) ∧ ((p7 ∨ p7) ∨ (True ∨ False))) → False) → ((((p2 → False) ∧ (p5 ∧ False)) → ((p7 → p4) ∨ (p3 → False))) ∨ (((False → p4) ∨ (p7 → False)) → False))) := by
  intro assump_10
  apply Or.inl
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_15
    case intro assump_18 assump_19 =>
      apply False.elim assump_19


variable (p3 p5 p6 p2 p7 p1 : Prop)
theorem file38_23209 : ((((((p7 → True) → False) → False) ∨ (((p1 ∧ p2) ∧ (p7 ∨ True)) → False)) ∧ ((((p5 → False) → False) ∧ ((p3 → False) ∨ (True ∨ p6))) ∧ (((p6 ∨ p1) ∨ (p1 → False)) → False))) → False) := by
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
            have assump_110 : ((p6 ∨ p1) ∨ (p1 → False)) := by
              apply Or.inr
              intro assump_21
              have assump_111 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_21
              let assump_25 := assump_9 assump_111
              apply False.elim assump_25
            let assump_20 := assump_9 assump_110
            apply False.elim assump_20
          case inr assump_15 =>
            cases assump_15
            case inl assump_32 =>
              have assump_112 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                apply Or.inr
                intro assump_39
                have assump_113 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_39
                let assump_43 := assump_9 assump_113
                apply False.elim assump_43
              let assump_38 := assump_9 assump_112
              apply False.elim assump_38
            case inr assump_33 =>
              have assump_114 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                apply Or.inl
                apply Or.inl
                exact assump_33
              let assump_54 := assump_9 assump_114
              apply False.elim assump_54
    case inr assump_5 =>
      cases assump_3
      case intro assump_60 assump_61 =>
        cases assump_60
        case intro assump_62 assump_63 =>
          cases assump_63
          case inl assump_66 =>
            have assump_115 : ((p6 ∨ p1) ∨ (p1 → False)) := by
              apply Or.inr
              intro assump_73
              have assump_116 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_73
              let assump_77 := assump_61 assump_116
              apply False.elim assump_77
            let assump_72 := assump_61 assump_115
            apply False.elim assump_72
          case inr assump_67 =>
            cases assump_67
            case inl assump_84 =>
              have assump_117 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                apply Or.inr
                intro assump_91
                have assump_118 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_91
                let assump_95 := assump_61 assump_118
                apply False.elim assump_95
              let assump_90 := assump_61 assump_117
              apply False.elim assump_90
            case inr assump_85 =>
              have assump_119 : ((p6 ∨ p1) ∨ (p1 → False)) := by
                apply Or.inl
                apply Or.inl
                exact assump_85
              let assump_106 := assump_61 assump_119
              apply False.elim assump_106


variable (p7 p3 p0 p4 p5 p2 p1 p6 : Prop)
theorem file38_26589 : (((((p7 ∧ p6) → (p0 → False)) → ((p5 ∧ False) ∧ (p3 ∨ False))) → False) → ((((p4 ∧ p1) → False) → ((True ∨ p6) ∨ (p2 → p7))) → (((p3 ∧ True) → (p5 → p0)) → ((p5 ∧ p1) ∨ (p7 ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p5 p2 : Prop)
theorem file38_26928 : (((((p5 → p2) → (True → False)) → ((p2 → False) ∨ (p2 → True))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p5 → p2) → (True → False)) → ((p2 → False) ∨ (p2 → True))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_24 : (p5 → p2) := by
      intro assump_13
      exact assump_8
    let assump_12 := assump_5 assump_24
    have assump_25 : True := by
      apply True.intro
    let assump_16 := assump_12 assump_25
    apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p0 p1 p4 p6 : Prop)
theorem file38_27544 : (((((True → False) → False) ∧ ((p6 ∧ p3) ∨ (p3 ∨ p6))) ∨ (((True ∨ p1) → False) → False)) ∨ ((((p4 → p0) ∧ (p1 → False)) ∧ ((True ∧ p0) → False)) ∨ (((p0 ∧ p1) ∨ (p6 → p1)) → False))) := by
  apply Or.inl
  apply Or.inr
  intro assump_8
  have assump_15 : (True ∨ p1) := by
    apply Or.inl
    apply True.intro
  let assump_11 := assump_8 assump_15
  apply False.elim assump_11


variable (p3 p1 p6 p7 p2 p0 p5 p4 : Prop)
theorem file38_27989 : ((((((p4 ∧ p7) → (p6 ∧ p1)) ∧ ((p3 ∨ p1) ∧ (p3 → p5))) ∧ (((p4 → False) ∨ (p3 ∧ p3)) → False)) ∧ ((((True ∨ p2) → (p7 ∧ p2)) ∧ ((True ∨ p4) → False)) ∧ (((p1 → True) ∨ (p7 → False)) → ((p2 → p1) ∧ (p0 ∧ p7))))) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_26
        case intro assump_29 assump_30 =>
          cases assump_29
          case inl assump_31 =>
            cases assump_22
            case intro assump_39 assump_40 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                have assump_87 : (True ∨ p4) := by
                  apply Or.inl
                  apply True.intro
                let assump_56 := assump_42 assump_87
                apply False.elim assump_56
          case inr assump_32 =>
            cases assump_22
            case intro assump_66 assump_67 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                have assump_88 : (True ∨ p4) := by
                  apply Or.inl
                  apply True.intro
                let assump_83 := assump_69 assump_88
                apply False.elim assump_83


variable (p5 p6 p4 p2 p7 p1 p0 : Prop)
theorem file38_29356 : (((((True → False) → (p5 ∨ p4)) → False) ∧ (((False → True) → (p7 → p6)) ∨ ((p4 ∧ p1) → False))) → ((((True ∨ p5) ∨ (p7 → False)) ∧ ((p0 ∧ p7) ∨ (p4 ∧ p2))) → (((True ∨ p6) ∧ (p2 → p6)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_13
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_1
                case intro assump_28 assump_29 =>
                  cases assump_29
                  case inl assump_32 =>
                    have assump_498 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_41
                      have assump_499 : True := by
                        apply True.intro
                      let assump_44 := assump_41 assump_499
                      apply False.elim assump_44
                    let assump_40 := assump_28 assump_498
                    apply False.elim assump_40
                  case inr assump_33 =>
                    have assump_500 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_55
                      have assump_501 : True := by
                        apply True.intro
                      let assump_58 := assump_55 assump_501
                      apply False.elim assump_58
                    let assump_54 := assump_28 assump_500
                    apply False.elim assump_54
            case inr assump_21 =>
              cases assump_21
              case intro assump_65 assump_66 =>
                cases assump_1
                case intro assump_71 assump_72 =>
                  cases assump_72
                  case inl assump_75 =>
                    have assump_502 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_83
                      apply Or.inr
                      exact assump_65
                    let assump_82 := assump_71 assump_502
                    apply False.elim assump_82
                  case inr assump_76 =>
                    have assump_503 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_93
                      apply Or.inr
                      exact assump_65
                    let assump_92 := assump_71 assump_503
                    apply False.elim assump_92
          case inr assump_17 =>
            cases assump_13
            case inl assump_101 =>
              cases assump_101
              case intro assump_103 assump_104 =>
                cases assump_1
                case intro assump_109 assump_110 =>
                  cases assump_110
                  case inl assump_113 =>
                    have assump_504 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_122
                      apply Or.inl
                      exact assump_17
                    let assump_121 := assump_109 assump_504
                    apply False.elim assump_121
                  case inr assump_114 =>
                    have assump_505 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_132
                      apply Or.inl
                      exact assump_17
                    let assump_131 := assump_109 assump_505
                    apply False.elim assump_131
            case inr assump_102 =>
              cases assump_102
              case intro assump_138 assump_139 =>
                cases assump_1
                case intro assump_144 assump_145 =>
                  cases assump_145
                  case inl assump_148 =>
                    have assump_506 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_156
                      apply Or.inl
                      exact assump_17
                    let assump_155 := assump_144 assump_506
                    apply False.elim assump_155
                  case inr assump_149 =>
                    have assump_507 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_166
                      apply Or.inl
                      exact assump_17
                    let assump_165 := assump_144 assump_507
                    apply False.elim assump_165
        case inr assump_15 =>
          cases assump_13
          case inl assump_174 =>
            cases assump_174
            case intro assump_176 assump_177 =>
              cases assump_1
              case intro assump_182 assump_183 =>
                cases assump_183
                case inl assump_186 =>
                  have assump_508 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_195
                    have assump_509 : True := by
                      apply True.intro
                    let assump_198 := assump_195 assump_509
                    apply False.elim assump_198
                  let assump_194 := assump_182 assump_508
                  apply False.elim assump_194
                case inr assump_187 =>
                  have assump_510 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_209
                    have assump_511 : True := by
                      apply True.intro
                    let assump_212 := assump_209 assump_511
                    apply False.elim assump_212
                  let assump_208 := assump_182 assump_510
                  apply False.elim assump_208
          case inr assump_175 =>
            cases assump_175
            case intro assump_219 assump_220 =>
              cases assump_1
              case intro assump_225 assump_226 =>
                cases assump_226
                case inl assump_229 =>
                  have assump_512 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_237
                    apply Or.inr
                    exact assump_219
                  let assump_236 := assump_225 assump_512
                  apply False.elim assump_236
                case inr assump_230 =>
                  have assump_513 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_247
                    apply Or.inr
                    exact assump_219
                  let assump_246 := assump_225 assump_513
                  apply False.elim assump_246
    case inr assump_7 =>
      cases assump_2
      case intro assump_257 assump_258 =>
        cases assump_257
        case inl assump_259 =>
          cases assump_259
          case inl assump_261 =>
            cases assump_258
            case inl assump_265 =>
              cases assump_265
              case intro assump_267 assump_268 =>
                cases assump_1
                case intro assump_273 assump_274 =>
                  cases assump_274
                  case inl assump_277 =>
                    have assump_514 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_286
                      have assump_515 : True := by
                        apply True.intro
                      let assump_289 := assump_286 assump_515
                      apply False.elim assump_289
                    let assump_285 := assump_273 assump_514
                    apply False.elim assump_285
                  case inr assump_278 =>
                    have assump_516 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_300
                      have assump_517 : True := by
                        apply True.intro
                      let assump_303 := assump_300 assump_517
                      apply False.elim assump_303
                    let assump_299 := assump_273 assump_516
                    apply False.elim assump_299
            case inr assump_266 =>
              cases assump_266
              case intro assump_310 assump_311 =>
                cases assump_1
                case intro assump_316 assump_317 =>
                  cases assump_317
                  case inl assump_320 =>
                    have assump_518 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_328
                      apply Or.inr
                      exact assump_310
                    let assump_327 := assump_316 assump_518
                    apply False.elim assump_327
                  case inr assump_321 =>
                    have assump_519 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_338
                      apply Or.inr
                      exact assump_310
                    let assump_337 := assump_316 assump_519
                    apply False.elim assump_337
          case inr assump_262 =>
            cases assump_258
            case inl assump_346 =>
              cases assump_346
              case intro assump_348 assump_349 =>
                cases assump_1
                case intro assump_354 assump_355 =>
                  cases assump_355
                  case inl assump_358 =>
                    have assump_520 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_367
                      apply Or.inl
                      exact assump_262
                    let assump_366 := assump_354 assump_520
                    apply False.elim assump_366
                  case inr assump_359 =>
                    have assump_521 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_377
                      apply Or.inl
                      exact assump_262
                    let assump_376 := assump_354 assump_521
                    apply False.elim assump_376
            case inr assump_347 =>
              cases assump_347
              case intro assump_383 assump_384 =>
                cases assump_1
                case intro assump_389 assump_390 =>
                  cases assump_390
                  case inl assump_393 =>
                    have assump_522 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_401
                      apply Or.inl
                      exact assump_262
                    let assump_400 := assump_389 assump_522
                    apply False.elim assump_400
                  case inr assump_394 =>
                    have assump_523 : ((True → False) → (p5 ∨ p4)) := by
                      intro assump_411
                      apply Or.inl
                      exact assump_262
                    let assump_410 := assump_389 assump_523
                    apply False.elim assump_410
        case inr assump_260 =>
          cases assump_258
          case inl assump_419 =>
            cases assump_419
            case intro assump_421 assump_422 =>
              cases assump_1
              case intro assump_427 assump_428 =>
                cases assump_428
                case inl assump_431 =>
                  have assump_524 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_440
                    have assump_525 : True := by
                      apply True.intro
                    let assump_443 := assump_440 assump_525
                    apply False.elim assump_443
                  let assump_439 := assump_427 assump_524
                  apply False.elim assump_439
                case inr assump_432 =>
                  have assump_526 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_454
                    have assump_527 : True := by
                      apply True.intro
                    let assump_457 := assump_454 assump_527
                    apply False.elim assump_457
                  let assump_453 := assump_427 assump_526
                  apply False.elim assump_453
          case inr assump_420 =>
            cases assump_420
            case intro assump_464 assump_465 =>
              cases assump_1
              case intro assump_470 assump_471 =>
                cases assump_471
                case inl assump_474 =>
                  have assump_528 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_482
                    apply Or.inr
                    exact assump_464
                  let assump_481 := assump_470 assump_528
                  apply False.elim assump_481
                case inr assump_475 =>
                  have assump_529 : ((True → False) → (p5 ∨ p4)) := by
                    intro assump_492
                    apply Or.inr
                    exact assump_464
                  let assump_491 := assump_470 assump_529
                  apply False.elim assump_491


variable (p2 p7 p0 p4 p5 p6 : Prop)
theorem file38_42101 : (((((p4 ∨ p0) → (p5 → False)) ∧ ((p6 → False) ∧ (p0 ∨ False))) → (((p2 ∨ p5) ∨ (p6 → p2)) ∨ ((True → p6) → (p7 → False)))) ∨ ((((p7 ∨ False) → False) ∨ ((False ∧ p0) → (False ∨ p6))) ∧ (((True ∧ p2) ∧ (p0 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        apply Or.inr
        intro assump_14
        have assump_25 : p6 := by
          exact assump_14
        let assump_19 := assump_6 assump_25
        apply False.elim assump_19
      case inr assump_11 =>
        apply False.elim assump_11


variable (p7 p1 p4 p0 p2 p6 : Prop)
theorem file38_42848 : (((((False ∨ p0) → False) → ((p4 ∨ p4) → (p6 → p1))) ∧ (((p4 ∧ False) → (p2 ∨ True)) → False)) → ((((p0 → False) ∧ (p7 ∨ p2)) → False) ∧ (((True ∨ p2) → False) ∨ ((p2 ∨ p0) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        have assump_83 : ((p4 ∧ False) → (p2 ∨ True)) := by
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
        let assump_17 := assump_12 assump_83
        apply False.elim assump_17
    case inr assump_8 =>
      cases assump_1
      case intro assump_30 assump_31 =>
        have assump_84 : ((p4 ∧ False) → (p2 ∨ True)) := by
          intro assump_37
          cases assump_37
          case intro assump_38 assump_39 =>
            apply False.elim assump_39
        let assump_36 := assump_31 assump_84
        apply False.elim assump_36
  cases assump_1
  case intro assump_47 assump_48 =>
    apply Or.inl
    intro assump_53
    cases assump_53
    case inl assump_54 =>
      have assump_85 : ((p4 ∧ False) → (p2 ∨ True)) := by
        intro assump_59
        cases assump_59
        case intro assump_60 assump_61 =>
          apply False.elim assump_61
      let assump_58 := assump_48 assump_85
      apply False.elim assump_58
    case inr assump_55 =>
      have assump_86 : ((p4 ∧ False) → (p2 ∨ True)) := by
        intro assump_73
        cases assump_73
        case intro assump_74 assump_75 =>
          apply False.elim assump_75
      let assump_72 := assump_48 assump_86
      apply False.elim assump_72


variable (p4 p0 p6 p7 p1 p3 p5 : Prop)
theorem file38_44630 : (((((True → False) → (p7 ∧ False)) ∨ ((True → False) → (True → p3))) ∨ (((False ∧ p0) ∨ (p6 → False)) → False)) ∨ ((((p5 → p7) → (p3 ∧ p5)) → ((False ∧ p0) ∨ (p3 ∨ p4))) ∧ (((False → False) → (p6 ∧ p0)) → ((True → False) ∨ (p1 ∨ p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_17
  apply And.intro
  have assump_30 : True := by
    apply True.intro
  let assump_20 := assump_17 assump_30
  apply False.elim assump_20
  have assump_31 : True := by
    apply True.intro
  let assump_26 := assump_17 assump_31
  apply False.elim assump_26


variable (p5 p6 p7 p1 p4 p0 p3 : Prop)
theorem file38_45255 : ((((((p4 ∨ p0) → False) ∧ ((p4 → False) → (p3 → p3))) ∧ (((p0 → p5) → False) ∧ ((p1 → False) ∧ (True → False)))) ∧ ((((p0 ∨ p7) ∨ (p6 ∧ p1)) ∧ ((p5 ∧ False) ∨ (p6 → p0))) ∧ (((p5 ∧ False) ∨ (p3 ∨ p6)) ∨ ((p7 ∨ p7) → (p3 → True))))) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            cases assump_8
            case intro assump_27 assump_28 =>
              cases assump_27
              case intro assump_29 assump_30 =>
                cases assump_29
                case inl assump_31 =>
                  cases assump_31
                  case inl assump_33 =>
                    cases assump_30
                    case inl assump_37 =>
                      cases assump_37
                      case intro assump_39 assump_40 =>
                        apply False.elim assump_40
                    case inr assump_38 =>
                      cases assump_28
                      case inl assump_47 =>
                        cases assump_47
                        case inl assump_49 =>
                          cases assump_49
                          case intro assump_51 assump_52 =>
                            apply False.elim assump_52
                        case inr assump_50 =>
                          cases assump_50
                          case inl assump_57 =>
                            have assump_201 : True := by
                              apply True.intro
                            let assump_64 := assump_22 assump_201
                            apply False.elim assump_64
                          case inr assump_58 =>
                            have assump_202 : True := by
                              apply True.intro
                            let assump_74 := assump_22 assump_202
                            apply False.elim assump_74
                      case inr assump_48 =>
                        have assump_203 : True := by
                          apply True.intro
                        let assump_83 := assump_22 assump_203
                        apply False.elim assump_83
                  case inr assump_34 =>
                    cases assump_30
                    case inl assump_89 =>
                      cases assump_89
                      case intro assump_91 assump_92 =>
                        apply False.elim assump_92
                    case inr assump_90 =>
                      cases assump_28
                      case inl assump_99 =>
                        cases assump_99
                        case inl assump_101 =>
                          cases assump_101
                          case intro assump_103 assump_104 =>
                            apply False.elim assump_104
                        case inr assump_102 =>
                          cases assump_102
                          case inl assump_109 =>
                            have assump_204 : True := by
                              apply True.intro
                            let assump_116 := assump_22 assump_204
                            apply False.elim assump_116
                          case inr assump_110 =>
                            have assump_205 : True := by
                              apply True.intro
                            let assump_126 := assump_22 assump_205
                            apply False.elim assump_126
                      case inr assump_100 =>
                        have assump_206 : True := by
                          apply True.intro
                        let assump_136 := assump_22 assump_206
                        apply False.elim assump_136
                case inr assump_32 =>
                  cases assump_32
                  case intro assump_140 assump_141 =>
                    cases assump_30
                    case inl assump_146 =>
                      cases assump_146
                      case intro assump_148 assump_149 =>
                        apply False.elim assump_149
                    case inr assump_147 =>
                      cases assump_28
                      case inl assump_156 =>
                        cases assump_156
                        case inl assump_158 =>
                          cases assump_158
                          case intro assump_160 assump_161 =>
                            apply False.elim assump_161
                        case inr assump_159 =>
                          cases assump_159
                          case inl assump_166 =>
                            have assump_207 : True := by
                              apply True.intro
                            let assump_175 := assump_22 assump_207
                            apply False.elim assump_175
                          case inr assump_167 =>
                            have assump_208 : True := by
                              apply True.intro
                            let assump_186 := assump_22 assump_208
                            apply False.elim assump_186
                      case inr assump_157 =>
                        have assump_209 : True := by
                          apply True.intro
                        let assump_197 := assump_22 assump_209
                        apply False.elim assump_197


variable (p5 p6 p1 p0 p7 p2 p3 : Prop)
theorem file38_50818 : ((((((False → True) ∨ (p5 ∧ p3)) → ((p0 → False) ∧ (p6 ∨ p6))) → (((p1 ∨ p7) ∧ (p0 → True)) → ((True ∧ False) → (True ∨ p7)))) ∧ ((((p2 ∧ True) ∨ (p2 → False)) ∨ ((p7 ∧ True) → (False → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p2 ∧ True) ∨ (p2 → False)) ∨ ((p7 ∧ True) → (False → p0))) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      have assump_21 : (((p2 ∧ True) ∨ (p2 → False)) ∨ ((p7 ∧ True) → (False → p0))) := by
        apply Or.inl
        apply Or.inl
        apply And.intro
        exact assump_9
        apply True.intro
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p5 p4 p2 p1 p6 p3 : Prop)
theorem file38_51660 : (((((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) → False) → ((((p5 ∧ False) ∨ (p3 → False)) ∨ ((p6 ∨ p5) ∧ (p2 ∧ True))) → (((p6 ∨ p2) ∨ (p2 ∧ True)) → ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_2
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
        case inr assump_16 =>
          have assump_202 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
            apply Or.inl
            intro assump_28
            have assump_203 : True := by
              apply True.intro
            let assump_31 := assump_28 assump_203
            apply False.elim assump_31
          let assump_27 := assump_1 assump_202
          apply False.elim assump_27
      case inr assump_14 =>
        cases assump_14
        case intro assump_38 assump_39 =>
          cases assump_38
          case inl assump_40 =>
            cases assump_39
            case intro assump_44 assump_45 =>
              have assump_204 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
                apply Or.inl
                intro assump_53
                apply Or.inr
                exact assump_44
              let assump_52 := assump_1 assump_204
              apply False.elim assump_52
          case inr assump_41 =>
            cases assump_39
            case intro assump_61 assump_62 =>
              have assump_205 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
                apply Or.inl
                intro assump_70
                apply Or.inr
                exact assump_61
              let assump_69 := assump_1 assump_205
              apply False.elim assump_69
    case inr assump_10 =>
      cases assump_2
      case inl assump_78 =>
        cases assump_78
        case inl assump_80 =>
          cases assump_80
          case intro assump_82 assump_83 =>
            apply False.elim assump_83
        case inr assump_81 =>
          have assump_206 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
            apply Or.inl
            intro assump_93
            apply Or.inr
            exact assump_10
          let assump_92 := assump_1 assump_206
          apply False.elim assump_92
      case inr assump_79 =>
        cases assump_79
        case intro assump_99 assump_100 =>
          cases assump_99
          case inl assump_101 =>
            cases assump_100
            case intro assump_105 assump_106 =>
              have assump_207 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
                apply Or.inl
                intro assump_114
                apply Or.inr
                exact assump_105
              let assump_113 := assump_1 assump_207
              apply False.elim assump_113
          case inr assump_102 =>
            cases assump_100
            case intro assump_122 assump_123 =>
              have assump_208 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
                apply Or.inl
                intro assump_131
                apply Or.inr
                exact assump_122
              let assump_130 := assump_1 assump_208
              apply False.elim assump_130
  case inr assump_8 =>
    cases assump_8
    case intro assump_137 assump_138 =>
      cases assump_2
      case inl assump_143 =>
        cases assump_143
        case inl assump_145 =>
          cases assump_145
          case intro assump_147 assump_148 =>
            apply False.elim assump_148
        case inr assump_146 =>
          have assump_209 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
            apply Or.inl
            intro assump_158
            apply Or.inr
            exact assump_137
          let assump_157 := assump_1 assump_209
          apply False.elim assump_157
      case inr assump_144 =>
        cases assump_144
        case intro assump_164 assump_165 =>
          cases assump_164
          case inl assump_166 =>
            cases assump_165
            case intro assump_170 assump_171 =>
              have assump_210 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
                apply Or.inl
                intro assump_179
                apply Or.inr
                exact assump_170
              let assump_178 := assump_1 assump_210
              apply False.elim assump_178
          case inr assump_167 =>
            cases assump_165
            case intro assump_187 assump_188 =>
              have assump_211 : (((True → False) → (p4 ∨ p2)) ∨ ((False ∨ p1) ∨ (p2 → p6))) := by
                apply Or.inl
                intro assump_196
                apply Or.inr
                exact assump_187
              let assump_195 := assump_1 assump_211
              apply False.elim assump_195


variable (p5 p7 p2 p3 p6 p4 p1 : Prop)
theorem file38_56784 : (((((p7 ∧ p7) ∨ (False → False)) → False) → (((p3 ∧ p5) → (p3 → False)) ∧ ((False ∧ p4) → (True ∧ p4)))) ∨ ((((False ∨ True) → False) ∨ ((True → p4) ∧ (p6 ∧ True))) ∧ (((p1 ∨ p2) ∧ (p5 ∨ p3)) ∨ ((True ∨ p7) → False)))) := by
  apply Or.inl
  intro assump_15
  apply And.intro
  intro assump_16
  intro assump_17
  cases assump_16
  case intro assump_20 assump_21 =>
    have assump_40 : ((p7 ∧ p7) ∨ (False → False)) := by
      apply Or.inr
      intro assump_29
      apply False.elim assump_29
    let assump_28 := assump_15 assump_40
    apply False.elim assump_28
  intro assump_35
  apply And.intro
  apply True.intro
  cases assump_35
  case intro assump_36 assump_37 =>
    apply False.elim assump_36


variable (p0 p2 p4 p6 p7 p3 : Prop)
theorem file38_57553 : (((((p2 ∧ True) → (p7 ∨ p4)) ∧ ((p0 ∧ p3) ∧ (True → False))) → False) ∧ ((((p7 ∨ p6) → (False → False)) → False) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_31 : True := by
          apply True.intro
        let assump_16 := assump_7 assump_31
        apply False.elim assump_16
  intro assump_20
  have assump_32 : ((p7 ∨ p6) → (False → False)) := by
    intro assump_24
    intro assump_25
    apply False.elim assump_25
  let assump_23 := assump_20 assump_32
  apply False.elim assump_23


variable (p6 p4 p7 p1 p0 p2 p3 : Prop)
theorem file38_58299 : (((((p1 → False) → False) → ((p7 ∧ False) → False)) ∨ (((p0 ∨ True) → False) ∨ ((p4 ∧ p4) → (p6 ∧ p1)))) ∨ ((((p4 ∨ p7) ∨ (p1 ∨ False)) ∨ ((False → False) → False)) ∨ (((p7 → p2) ∨ (p3 → p2)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p6 p5 p4 p3 p0 p7 p1 : Prop)
theorem file38_58716 : (((((p4 ∨ p4) → False) ∨ ((p4 ∧ p5) ∧ (p7 → p1))) → (((p7 ∧ p7) ∧ (p1 ∧ p3)) → ((p7 → False) → (p6 → False)))) ∧ ((((p5 → p6) ∧ (p1 ∧ p6)) ∨ ((p3 ∨ False) → (p4 ∨ False))) → (((False → False) ∨ (p6 → p0)) ∨ ((p7 ∨ p6) ∨ (True ∧ p3))))) := by
  apply And.intro
  intro assump_11
  intro assump_12
  intro assump_13
  intro assump_14
  cases assump_12
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      cases assump_20
      case intro assump_27 assump_28 =>
        cases assump_11
        case inl assump_33 =>
          have assump_89 : p7 := by
            exact assump_22
          let assump_42 := assump_13 assump_89
          apply False.elim assump_42
        case inr assump_34 =>
          cases assump_34
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              have assump_90 : p7 := by
                exact assump_22
              let assump_64 := assump_13 assump_90
              apply False.elim assump_64
  intro assump_68
  cases assump_68
  case inl assump_69 =>
    cases assump_69
    case intro assump_71 assump_72 =>
      cases assump_72
      case intro assump_75 assump_76 =>
        apply Or.inl
        apply Or.inl
        intro assump_81
        apply False.elim assump_81
  case inr assump_70 =>
    apply Or.inl
    apply Or.inl
    intro assump_86
    apply False.elim assump_86


variable (p4 p7 p6 p0 p2 : Prop)
theorem file38_60209 : ((((((p0 → False) → (p7 → False)) → False) → (((p2 ∨ p2) → (p0 → p4)) ∨ ((p6 ∧ p6) → (p2 → True)))) → False) → False) := by
  intro assump_1
  have assump_53 : ((((p0 → False) → (p7 → False)) → False) → (((p2 ∨ p2) → (p0 → p4)) ∨ ((p6 ∧ p6) → (p2 → True)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case inl assump_12 =>
      have assump_54 : ((p0 → False) → (p7 → False)) := by
        intro assump_19
        intro assump_20
        have assump_55 : p0 := by
          exact assump_9
        let assump_25 := assump_19 assump_55
        apply False.elim assump_25
      let assump_18 := assump_5 assump_54
      apply False.elim assump_18
    case inr assump_13 =>
      have assump_56 : ((p0 → False) → (p7 → False)) := by
        intro assump_37
        intro assump_38
        have assump_57 : p0 := by
          exact assump_9
        let assump_43 := assump_37 assump_57
        apply False.elim assump_43
      let assump_36 := assump_5 assump_56
      apply False.elim assump_36
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p2 p4 p5 p7 p0 p6 p3 : Prop)
theorem file38_61388 : ((((((True → p5) ∧ (p6 ∧ p2)) → ((p6 → False) → False)) ∧ (((p3 ∧ True) ∨ (p7 → p0)) → False)) ∧ ((((p4 → p7) ∧ (False ∧ p7)) → False) ∧ (((False → False) → (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_24 : ((False → False) → (False → False)) := by
          intro assump_17
          intro assump_18
          apply False.elim assump_18
        let assump_16 := assump_11 assump_24
        apply False.elim assump_16


variable (p3 p5 p4 p0 p2 p1 p6 : Prop)
theorem file38_62071 : (((((p5 → False) → False) → False) ∧ (((False → False) ∧ (p2 → p6)) → ((p4 ∧ False) ∨ (p0 ∧ p4)))) → ((((p0 ∨ p6) → False) → ((p1 ∧ p2) → (p2 ∨ p5))) ∨ (((p1 ∧ p3) ∧ (p1 ∧ p6)) ∨ ((p2 → p1) → (False → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply Or.inl
      exact assump_11


variable (p1 p4 p2 p6 p0 p3 : Prop)
theorem file38_62570 : ((((((p3 ∨ p3) → False) → ((p1 → False) ∨ (p6 ∨ p4))) → (((p2 → p6) → (p0 → False)) → ((p3 → True) ∨ (p1 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p3 ∨ p3) → False) → ((p1 → False) ∨ (p6 ∨ p4))) → (((p2 → p6) → (p0 → False)) → ((p3 → True) ∨ (p1 ∧ p6)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    intro assump_11
    apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p7 p6 p3 p2 p0 p4 : Prop)
theorem file38_63086 : (((((p0 → p4) → (p6 → False)) → ((False → False) → (p6 ∧ False))) ∨ (((p3 ∨ p3) ∧ (p1 → False)) → ((p6 → p2) → (p0 → False)))) → ((((True → False) → (p3 → False)) → ((False ∨ p7) → (p7 → False))) → (((p1 → False) ∨ (p4 ∧ p7)) → ((False ∨ False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply False.elim assump_5
  case inr assump_6 =>
    apply False.elim assump_6


variable (p0 p7 p1 p3 p4 : Prop)
theorem file38_63597 : (((((p3 ∧ p7) ∧ (True → False)) → False) ∧ (((p3 → True) ∨ (p0 → p7)) → False)) → ((((False ∧ p4) → False) ∨ ((False ∧ p1) ∨ (p0 → True))) ∧ (((p3 → p7) → False) → False))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  intro assump_13
  cases assump_1
  case intro assump_16 assump_17 =>
    have assump_27 : ((p3 → True) ∨ (p0 → p7)) := by
      apply Or.inl
      intro assump_23
      apply True.intro
    let assump_22 := assump_17 assump_27
    apply False.elim assump_22


variable (p6 p0 p2 : Prop)
theorem file38_64297 : (((((p6 → False) ∧ (p0 → True)) → False) ∧ (((True ∧ True) ∨ (True ∧ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((True ∧ True) ∨ (True ∧ p2)) := by
      apply Or.inl
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p3 p6 p2 p7 p1 p4 p0 p5 : Prop)
theorem file38_64743 : ((((((p3 → False) → False) ∧ ((p1 ∨ p0) → (p0 → False))) → (((p0 → False) ∨ (p0 ∧ False)) ∨ ((p4 ∧ p7) → (p4 ∨ p0)))) → ((((p1 ∨ True) ∨ (True ∧ p3)) ∨ ((p6 ∨ p1) ∧ (p2 ∧ p5))) → False)) → False) := by
  intro assump_1
  have assump_25 : ((((p3 → False) → False) ∧ ((p1 ∨ p0) → (p0 → False))) → (((p0 → False) ∨ (p0 ∧ False)) ∨ ((p4 ∧ p7) → (p4 ∨ p0)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      have assump_26 : (p1 ∨ p0) := by
        apply Or.inr
        exact assump_12
      let assump_16 := assump_7 assump_26
      have assump_27 : p0 := by
        exact assump_12
      let assump_17 := assump_16 assump_27
      apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  have assump_28 : (((p1 ∨ True) ∨ (True ∧ p3)) ∨ ((p6 ∨ p1) ∧ (p2 ∧ p5))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_21 := assump_4 assump_28
  apply False.elim assump_21


variable (p3 p0 p7 p6 p1 : Prop)
theorem file38_65809 : ((((((p1 → p3) → (p0 → False)) ∧ ((True → p7) ∧ (p1 ∧ False))) → (((p7 → p6) → False) ∨ ((False ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 → p3) → (p0 → False)) ∧ ((True → p7) ∧ (p1 ∧ False))) → (((p7 → p6) → False) ∨ ((False ∧ p3) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p6 p2 p3 p1 p0 : Prop)
theorem file38_66462 : (((((p3 ∧ p6) → False) → False) ∧ (((p5 ∨ p1) ∨ (p2 → p0)) → False)) → ((((p6 → True) ∧ (p5 ∨ p0)) ∧ ((p6 → False) ∧ (True → p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_1
          case intro assump_19 assump_20 =>
            have assump_50 : ((p5 ∨ p1) ∨ (p2 → p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_9
            let assump_25 := assump_20 assump_50
            apply False.elim assump_25
      case inr assump_10 =>
        cases assump_4
        case intro assump_31 assump_32 =>
          cases assump_1
          case intro assump_37 assump_38 =>
            have assump_51 : ((p5 ∨ p1) ∨ (p2 → p0)) := by
              apply Or.inr
              intro assump_44
              exact assump_10
            let assump_43 := assump_38 assump_51
            apply False.elim assump_43


variable (p1 p0 p3 p4 p7 p2 p5 p6 : Prop)
theorem file38_67623 : (((((p5 ∨ p6) ∧ (True → False)) ∧ ((p0 → False) ∧ (p2 → False))) → False) ∨ ((((p2 → p6) ∧ (False ∧ p3)) → False) ∨ (((p4 → False) ∨ (p2 ∧ p2)) → ((p5 ∧ p7) ∧ (p3 ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          have assump_40 : True := by
            apply True.intro
          let assump_20 := assump_5 assump_40
          apply False.elim assump_20
      case inr assump_7 =>
        cases assump_3
        case intro assump_28 assump_29 =>
          have assump_41 : True := by
            apply True.intro
          let assump_36 := assump_5 assump_41
          apply False.elim assump_36


variable (p2 p5 p4 p7 p0 p6 p3 : Prop)
theorem file38_68508 : (((((p6 ∨ p6) → (p0 → False)) ∧ ((p5 ∧ p7) → (p3 ∨ p2))) → (((False ∨ True) → False) → False)) ∨ ((((p0 → p4) → False) → False) → False)) := by
  apply Or.inl
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    have assump_26 : (False ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_22 := assump_11 assump_26
    apply False.elim assump_22


variable (p3 p4 p6 p5 p7 p0 p2 : Prop)
theorem file38_68976 : ((((((p2 → p6) → False) → False) → False) ∧ ((((True → False) ∧ (True ∧ p7)) ∧ ((p5 → p7) → (p4 ∧ p0))) ∧ (((p6 ∨ p3) ∧ (False ∨ p2)) → False))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_16
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          cases assump_24
          case intro assump_27 assump_28 =>
            have assump_50 : True := by
              apply True.intro
            let assump_46 := assump_23 assump_50
            apply False.elim assump_46


variable (p3 p5 p1 p6 p4 p7 p2 : Prop)
theorem file38_69686 : (((((p7 ∧ p2) → False) → ((p7 → False) → (p2 ∧ p5))) ∨ (((p1 ∧ p6) ∨ (p5 ∨ p2)) ∨ ((p1 ∧ p5) ∧ (False → False)))) → ((((p2 ∨ p3) → False) → ((p6 ∧ False) → (p4 → p1))) ∨ (((p4 → p3) → (p7 ∨ p6)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  case inr assump_3 =>
    cases assump_3
    case inl assump_17 =>
      cases assump_17
      case inl assump_19 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          apply Or.inl
          intro assump_27
          intro assump_28
          intro assump_29
          cases assump_28
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
      case inr assump_20 =>
        cases assump_20
        case inl assump_38 =>
          apply Or.inl
          intro assump_42
          intro assump_43
          intro assump_44
          cases assump_43
          case intro assump_47 assump_48 =>
            apply False.elim assump_48
        case inr assump_39 =>
          apply Or.inl
          intro assump_55
          intro assump_56
          intro assump_57
          cases assump_56
          case intro assump_60 assump_61 =>
            apply False.elim assump_61
    case inr assump_18 =>
      cases assump_18
      case intro assump_66 assump_67 =>
        cases assump_66
        case intro assump_68 assump_69 =>
          apply Or.inl
          intro assump_76
          intro assump_77
          intro assump_78
          cases assump_77
          case intro assump_81 assump_82 =>
            apply False.elim assump_82


variable (p4 p2 p0 p6 p5 p3 p1 : Prop)
theorem file38_71472 : (((((p1 ∧ p0) ∧ (True → False)) ∧ ((p6 ∧ p0) → False)) ∧ (((p5 ∧ p4) → (p2 ∧ p6)) ∨ ((True ∨ p0) → (p0 ∧ p3)))) → False) := by
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          cases assump_18
          case inl assump_33 =>
            have assump_54 : True := by
              apply True.intro
            let assump_39 := assump_22 assump_54
            apply False.elim assump_39
          case inr assump_34 =>
            have assump_55 : True := by
              apply True.intro
            let assump_50 := assump_22 assump_55
            apply False.elim assump_50


variable (p3 p7 p5 p4 p0 : Prop)
theorem file38_72322 : (((((p7 → False) → (p4 → False)) ∧ ((p5 → False) → False)) → (((False ∧ p0) → False) ∨ ((True → False) → False))) → ((((p4 → False) → False) ∧ ((p0 ∧ p3) ∧ (True ∧ False))) → False)) := by
  intro assump_18
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_25
        case intro assump_32 assump_33 =>
          apply False.elim assump_33


variable (p3 p7 p0 p6 p4 p1 : Prop)
theorem file38_72884 : (((((p6 → p7) → False) → ((False → p3) ∧ (False ∨ True))) ∨ (((p6 → False) → (p0 ∨ p7)) → False)) ∨ ((((p3 → p4) → False) ∨ ((p1 → False) → (p0 → False))) ∧ (((p1 ∨ p3) ∧ (p3 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_19
  apply And.intro
  intro assump_20
  apply False.elim assump_20
  apply Or.inr
  apply True.intro


variable (p7 p0 p6 p2 p3 p1 p4 : Prop)
theorem file38_73296 : (((((p4 ∨ p3) ∨ (p0 ∨ p3)) ∧ ((p4 → False) ∧ (p1 ∧ p6))) → False) → ((((p2 ∧ p0) ∧ (False ∧ p1)) ∧ ((p0 ∧ p0) → (p7 ∧ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case intro assump_13 assump_14 =>
          apply False.elim assump_13


variable (p0 p5 p7 p2 p6 p1 : Prop)
theorem file38_73799 : (((((p0 ∨ p0) → (p5 → p2)) → False) → (((p1 → False) → (p6 → p5)) → ((True ∧ p2) → (p0 → p7)))) ∨ ((((p7 ∨ True) → (p7 → p5)) ∧ ((p7 ∨ False) ∨ (p7 ∨ p0))) ∨ (((p1 → p2) ∨ (p0 ∨ False)) → ((p6 ∧ p1) ∧ (True ∧ p2))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    have assump_31 : ((p0 ∨ p0) → (p5 → p2)) := by
      intro assump_18
      intro assump_19
      cases assump_18
      case inl assump_22 =>
        exact assump_8
      case inr assump_23 =>
        exact assump_8
    let assump_17 := assump_1 assump_31
    apply False.elim assump_17


variable (p7 p4 p3 p5 p0 p1 : Prop)
theorem file38_74506 : (((((p0 ∨ True) → False) → ((p4 ∧ p7) → (p3 ∨ p1))) ∨ (((False → p3) ∧ (p5 ∨ p4)) ∨ ((p7 ∧ p4) → False))) ∨ ((((True ∨ False) ∧ (True ∨ p0)) → ((True → p5) ∨ (p5 → p7))) ∧ (((True → False) → False) ∨ ((p4 → False) ∨ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_15 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_11 := assump_1 assump_15
    apply False.elim assump_11


variable (p1 p3 p2 p6 p4 p5 p7 : Prop)
theorem file38_75075 : (((((p2 → False) ∧ (p4 ∨ p5)) ∨ ((p4 ∨ p7) → False)) ∧ (((True → False) → False) ∧ ((p1 ∨ p2) → (False ∧ p7)))) → ((((p4 ∧ p2) ∧ (p7 ∨ False)) → False) ∨ (((False ∧ p3) → False) ∧ ((p6 ∧ p2) ∧ (p1 ∨ p1))))) := by
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
          case intro assump_14 assump_15 =>
            apply Or.inl
            intro assump_20
            cases assump_20
            case intro assump_21 assump_22 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                cases assump_22
                case inl assump_29 =>
                  have assump_105 : (p1 ∨ p2) := by
                    apply Or.inr
                    exact assump_24
                  let assump_36 := assump_15 assump_105
                  let assump_37 := And.left assump_36
                  apply False.elim assump_37
                case inr assump_30 =>
                  apply False.elim assump_30
        case inr assump_11 =>
          cases assump_3
          case intro assump_45 assump_46 =>
            apply Or.inl
            intro assump_51
            cases assump_51
            case intro assump_52 assump_53 =>
              cases assump_52
              case intro assump_54 assump_55 =>
                cases assump_53
                case inl assump_60 =>
                  have assump_106 : (p1 ∨ p2) := by
                    apply Or.inr
                    exact assump_55
                  let assump_67 := assump_46 assump_106
                  let assump_68 := And.left assump_67
                  apply False.elim assump_68
                case inr assump_61 =>
                  apply False.elim assump_61
    case inr assump_5 =>
      cases assump_3
      case intro assump_76 assump_77 =>
        apply Or.inl
        intro assump_82
        cases assump_82
        case intro assump_83 assump_84 =>
          cases assump_83
          case intro assump_85 assump_86 =>
            cases assump_84
            case inl assump_91 =>
              have assump_107 : (p1 ∨ p2) := by
                apply Or.inr
                exact assump_86
              let assump_98 := assump_77 assump_107
              let assump_99 := And.left assump_98
              apply False.elim assump_99
            case inr assump_92 =>
              apply False.elim assump_92


variable (p6 p1 p2 : Prop)
theorem file38_77655 : ((((((True ∨ p6) → False) → ((p6 ∧ p2) → (p1 → p2))) ∨ (((p1 ∧ False) → False) ∧ ((False ∧ p1) → (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((True ∨ p6) → False) → ((p6 ∧ p2) → (p1 → p2))) ∨ (((p1 ∧ False) → False) ∧ ((False ∧ p1) → (p2 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      exact assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p5 p3 p7 p6 p0 : Prop)
theorem file38_78220 : ((((((p7 ∧ p3) → False) → False) → (((p7 → False) → False) ∨ ((False → p0) ∨ (p5 → p6)))) → False) → False) := by
  intro assump_9
  have assump_40 : ((((p7 ∧ p3) → False) → False) → (((p7 → False) → False) ∨ ((False → p0) ∨ (p5 → p6)))) := by
    intro assump_13
    apply Or.inl
    intro assump_16
    have assump_41 : ((p7 ∧ p3) → False) := by
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        have assump_42 : p7 := by
          exact assump_22
        let assump_30 := assump_16 assump_42
        apply False.elim assump_30
    let assump_20 := assump_13 assump_41
    apply False.elim assump_20
  let assump_12 := assump_9 assump_40
  apply False.elim assump_12


variable (p0 p4 p5 p3 p6 p1 p7 : Prop)
theorem file38_78994 : (((((True → False) → False) ∨ ((True ∧ True) → False)) ∧ (((p4 → p4) → False) → ((p7 ∧ p1) ∧ (p5 ∧ False)))) ∨ ((((p0 ∧ p3) ∨ (p6 ∧ p1)) → False) ∧ (((p5 → False) → (p3 ∨ p3)) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_45 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4
  intro assump_8
  apply And.intro
  apply And.intro
  have assump_46 : (p4 → p4) := by
    intro assump_12
    exact assump_12
  let assump_11 := assump_8 assump_46
  apply False.elim assump_11
  have assump_47 : (p4 → p4) := by
    intro assump_21
    exact assump_21
  let assump_20 := assump_8 assump_47
  apply False.elim assump_20
  apply And.intro
  have assump_48 : (p4 → p4) := by
    intro assump_30
    exact assump_30
  let assump_29 := assump_8 assump_48
  apply False.elim assump_29
  have assump_49 : (p4 → p4) := by
    intro assump_39
    exact assump_39
  let assump_38 := assump_8 assump_49
  apply False.elim assump_38


variable (p2 p5 p3 p4 p7 : Prop)
theorem file38_80064 : ((((((True ∨ False) → False) → ((p7 ∧ False) ∧ (p7 → False))) → (((p7 → False) → (p4 → False)) ∧ ((p2 ∧ p3) ∨ (p5 ∨ p5)))) ∧ ((((p2 → False) ∧ (p7 ∧ False)) → False) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_34 : (((p2 → False) ∧ (p7 ∧ False)) → False) := by
      intro assump_20
      cases assump_20
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
    let assump_19 := assump_14 assump_34
    apply False.elim assump_19


variable (p7 p1 p5 p4 p2 p6 p0 p3 : Prop)
theorem file38_80719 : ((((((p7 → False) ∨ (p1 → False)) ∨ ((p7 ∧ p0) ∧ (p0 → False))) ∨ (((p4 ∨ p1) ∧ (p7 → False)) ∨ ((p1 → p7) ∧ (p2 ∧ False)))) ∧ ((((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_110 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
            apply Or.inl
            apply Or.inr
            intro assump_15
            have assump_111 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_15
            let assump_19 := assump_3 assump_111
            apply False.elim assump_19
          let assump_14 := assump_3 assump_110
          apply False.elim assump_14
        case inr assump_9 =>
          have assump_112 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
            apply Or.inl
            apply Or.inr
            intro assump_31
            have assump_113 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_31
            let assump_35 := assump_3 assump_113
            apply False.elim assump_35
          let assump_30 := assump_3 assump_112
          apply False.elim assump_30
      case inr assump_7 =>
        cases assump_7
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            have assump_114 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
              apply Or.inl
              apply Or.inr
              intro assump_55
              have assump_115 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_55
              let assump_59 := assump_3 assump_115
              apply False.elim assump_59
            let assump_54 := assump_3 assump_114
            apply False.elim assump_54
    case inr assump_5 =>
      cases assump_5
      case inl assump_66 =>
        cases assump_66
        case intro assump_68 assump_69 =>
          cases assump_68
          case inl assump_70 =>
            have assump_116 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_70
            let assump_78 := assump_3 assump_116
            apply False.elim assump_78
          case inr assump_71 =>
            have assump_117 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
              apply Or.inl
              apply Or.inr
              intro assump_89
              have assump_118 : (((p4 ∨ p2) ∨ (p2 → p6)) ∨ ((p2 ∨ p3) ∨ (True ∧ p5))) := by
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_89
              let assump_93 := assump_3 assump_118
              apply False.elim assump_93
            let assump_88 := assump_3 assump_117
            apply False.elim assump_88
      case inr assump_67 =>
        cases assump_67
        case intro assump_100 assump_101 =>
          cases assump_101
          case intro assump_104 assump_105 =>
            apply False.elim assump_105


variable (p4 p2 p0 p7 p6 p5 : Prop)
theorem file38_84325 : ((((((p6 ∧ p7) → False) → ((p0 ∧ True) ∨ (p7 → False))) ∧ (((p2 ∧ True) → (True → False)) ∧ ((False → p4) → False))) ∧ ((((True ∧ p6) ∨ (p0 ∨ p6)) ∧ ((p4 → False) ∧ (False ∨ p2))) → (((p5 → p7) → False) → ((p5 ∨ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_24 : (False → p4) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_9 assump_24
        apply False.elim assump_17


variable (p6 p0 p1 p4 p3 p2 p5 : Prop)
theorem file38_84999 : ((((((p1 → p6) → False) → ((False ∧ p4) ∧ (p0 ∨ True))) ∧ (((p0 → p1) ∨ (p2 ∨ p0)) → False)) ∧ ((((p0 ∧ p6) → (False → False)) → ((p3 ∧ p5) → (p0 → False))) ∧ (((False ∨ p2) → False) ∧ ((False ∨ False) ∧ (p6 ∧ p1))))) → False) := by
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
            case inl assump_20 =>
              apply False.elim assump_20
            case inr assump_21 =>
              apply False.elim assump_21


variable (p6 p0 p3 : Prop)
theorem file38_85781 : ((((((p0 ∨ p3) → False) → False) ∧ (((p6 ∨ False) → False) → False)) ∧ ((((p6 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : (((p6 ∨ True) → False) → False) := by
        intro assump_13
        have assump_24 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_16 := assump_13 assump_24
        apply False.elim assump_16
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p2 p1 p7 p4 p3 p5 : Prop)
theorem file38_86426 : (((((p5 ∧ p4) → False) ∧ ((True ∨ p1) → False)) ∧ (((p7 ∧ p5) ∧ (p2 ∧ p3)) ∨ ((p4 ∧ p3) → (p3 ∧ False)))) → ((((p3 ∧ p1) ∨ (p5 → False)) → ((p1 → False) ∨ (True → False))) → (((True → False) ∨ (p3 → p5)) → ((p7 ∧ p3) → (True → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply True.intro


variable (p4 p1 p5 p7 p0 : Prop)
theorem file38_86830 : (((((True ∧ False) → False) → False) ∧ (((p4 ∨ True) → False) ∨ ((False → p5) ∨ (False ∨ p4)))) → ((((p5 → False) ∨ (False ∧ p1)) ∧ ((p1 ∨ p0) ∧ (False → False))) ∨ (((False → p5) ∧ (False → False)) ∧ ((False ∧ p0) ∧ (p7 ∧ p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_106 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_24 := assump_6 assump_106
      apply False.elim assump_24
    case inr assump_7 =>
      cases assump_7
      case inl assump_28 =>
        have assump_107 : ((True ∧ False) → False) := by
          intro assump_56
          cases assump_56
          case intro assump_57 assump_58 =>
            apply False.elim assump_58
        let assump_55 := assump_2 assump_107
        apply False.elim assump_55
      case inr assump_29 =>
        cases assump_29
        case inl assump_66 =>
          apply False.elim assump_66
        case inr assump_67 =>
          have assump_108 : ((True ∧ False) → False) := by
            intro assump_96
            cases assump_96
            case intro assump_97 assump_98 =>
              apply False.elim assump_98
          let assump_95 := assump_2 assump_108
          apply False.elim assump_95


variable (p7 p4 p1 p2 p6 p0 : Prop)
theorem file38_88184 : (((((False → p2) ∨ (True → p7)) ∨ ((p1 → False) ∨ (p2 ∨ p1))) ∧ (((True ∨ p4) ∨ (p6 → p7)) → False)) → ((((p4 ∨ p4) → (p1 → False)) ∧ ((p4 ∨ p0) → (p2 → p6))) ∧ (((p7 ∧ p1) → (False ∨ p1)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          have assump_275 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_20 := assump_11 assump_275
          apply False.elim assump_20
        case inr assump_15 =>
          have assump_276 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_28 := assump_11 assump_276
          apply False.elim assump_28
      case inr assump_13 =>
        cases assump_13
        case inl assump_32 =>
          have assump_277 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_38 := assump_11 assump_277
          apply False.elim assump_38
        case inr assump_33 =>
          cases assump_33
          case inl assump_42 =>
            have assump_278 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_48 := assump_11 assump_278
            apply False.elim assump_48
          case inr assump_43 =>
            have assump_279 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_56 := assump_11 assump_279
            apply False.elim assump_56
  case inr assump_7 =>
    cases assump_1
    case intro assump_62 assump_63 =>
      cases assump_62
      case inl assump_64 =>
        cases assump_64
        case inl assump_66 =>
          have assump_280 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_72 := assump_63 assump_280
          apply False.elim assump_72
        case inr assump_67 =>
          have assump_281 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_80 := assump_63 assump_281
          apply False.elim assump_80
      case inr assump_65 =>
        cases assump_65
        case inl assump_84 =>
          have assump_282 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_90 := assump_63 assump_282
          apply False.elim assump_90
        case inr assump_85 =>
          cases assump_85
          case inl assump_94 =>
            have assump_283 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_100 := assump_63 assump_283
            apply False.elim assump_100
          case inr assump_95 =>
            have assump_284 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_108 := assump_63 assump_284
            apply False.elim assump_108
  intro assump_112
  intro assump_113
  cases assump_112
  case inl assump_116 =>
    cases assump_1
    case intro assump_120 assump_121 =>
      cases assump_120
      case inl assump_122 =>
        cases assump_122
        case inl assump_124 =>
          have assump_285 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_130 := assump_121 assump_285
          apply False.elim assump_130
        case inr assump_125 =>
          have assump_286 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_138 := assump_121 assump_286
          apply False.elim assump_138
      case inr assump_123 =>
        cases assump_123
        case inl assump_142 =>
          have assump_287 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_148 := assump_121 assump_287
          apply False.elim assump_148
        case inr assump_143 =>
          cases assump_143
          case inl assump_152 =>
            have assump_288 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_158 := assump_121 assump_288
            apply False.elim assump_158
          case inr assump_153 =>
            have assump_289 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_166 := assump_121 assump_289
            apply False.elim assump_166
  case inr assump_117 =>
    cases assump_1
    case intro assump_172 assump_173 =>
      cases assump_172
      case inl assump_174 =>
        cases assump_174
        case inl assump_176 =>
          have assump_290 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_182 := assump_173 assump_290
          apply False.elim assump_182
        case inr assump_177 =>
          have assump_291 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_190 := assump_173 assump_291
          apply False.elim assump_190
      case inr assump_175 =>
        cases assump_175
        case inl assump_194 =>
          have assump_292 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_200 := assump_173 assump_292
          apply False.elim assump_200
        case inr assump_195 =>
          cases assump_195
          case inl assump_204 =>
            have assump_293 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_210 := assump_173 assump_293
            apply False.elim assump_210
          case inr assump_205 =>
            have assump_294 : ((True ∨ p4) ∨ (p6 → p7)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_218 := assump_173 assump_294
            apply False.elim assump_218
  intro assump_222
  cases assump_1
  case intro assump_225 assump_226 =>
    cases assump_225
    case inl assump_227 =>
      cases assump_227
      case inl assump_229 =>
        have assump_295 : ((True ∨ p4) ∨ (p6 → p7)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_235 := assump_226 assump_295
        apply False.elim assump_235
      case inr assump_230 =>
        have assump_296 : ((True ∨ p4) ∨ (p6 → p7)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_243 := assump_226 assump_296
        apply False.elim assump_243
    case inr assump_228 =>
      cases assump_228
      case inl assump_247 =>
        have assump_297 : ((True ∨ p4) ∨ (p6 → p7)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_253 := assump_226 assump_297
        apply False.elim assump_253
      case inr assump_248 =>
        cases assump_248
        case inl assump_257 =>
          have assump_298 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_263 := assump_226 assump_298
          apply False.elim assump_263
        case inr assump_258 =>
          have assump_299 : ((True ∨ p4) ∨ (p6 → p7)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_271 := assump_226 assump_299
          apply False.elim assump_271


variable (p7 p4 p5 p3 p6 p1 : Prop)
theorem file38_96414 : (((((p7 → p4) ∨ (True ∨ True)) ∨ ((p1 ∨ p6) → False)) ∧ (((p3 ∧ False) → (p5 → p4)) → False)) → ((((False ∧ p5) → (p3 → False)) ∧ ((p3 ∨ p4) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          have assump_89 : ((p3 ∧ False) → (p5 → p4)) := by
            intro assump_20
            intro assump_21
            cases assump_20
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
          let assump_19 := assump_10 assump_89
          apply False.elim assump_19
        case inr assump_14 =>
          cases assump_14
          case inl assump_33 =>
            have assump_90 : ((p3 ∧ False) → (p5 → p4)) := by
              intro assump_40
              intro assump_41
              cases assump_40
              case intro assump_44 assump_45 =>
                apply False.elim assump_45
            let assump_39 := assump_10 assump_90
            apply False.elim assump_39
          case inr assump_34 =>
            have assump_91 : ((p3 ∧ False) → (p5 → p4)) := by
              intro assump_58
              intro assump_59
              cases assump_58
              case intro assump_62 assump_63 =>
                apply False.elim assump_63
            let assump_57 := assump_10 assump_91
            apply False.elim assump_57
      case inr assump_12 =>
        have assump_92 : ((p3 ∧ False) → (p5 → p4)) := by
          intro assump_76
          intro assump_77
          cases assump_76
          case intro assump_80 assump_81 =>
            apply False.elim assump_81
        let assump_75 := assump_10 assump_92
        apply False.elim assump_75


variable (p4 p7 p2 p0 : Prop)
theorem file38_98303 : ((((((p0 → p2) ∧ (True → False)) ∧ ((p2 → p4) ∧ (p7 ∧ p0))) → False) → False) → False) := by
  intro assump_11
  have assump_44 : ((((p0 → p2) ∧ (True → False)) ∧ ((p2 → p4) ∧ (p7 ∧ p0))) → False) := by
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_17
        case intro assump_24 assump_25 =>
          cases assump_25
          case intro assump_28 assump_29 =>
            have assump_45 : True := by
              apply True.intro
            let assump_37 := assump_19 assump_45
            apply False.elim assump_37
  let assump_14 := assump_11 assump_44
  apply False.elim assump_14


variable (p6 p0 p7 p1 p2 : Prop)
theorem file38_99066 : ((((((False → False) → False) → False) ∧ (((p1 → p7) → (p0 → True)) ∨ ((p6 → False) ∧ (True ∧ p6)))) → ((((p2 ∨ True) ∨ (p7 ∧ p7)) ∨ ((p1 ∨ p6) ∧ (p2 → p6))) → False)) → False) := by
  intro assump_1
  have assump_21 : ((((False → False) → False) → False) ∧ (((p1 → p7) → (p0 → True)) ∨ ((p6 → False) ∧ (True ∧ p6)))) := by
    apply And.intro
    intro assump_5
    have assump_22 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
    apply Or.inl
    intro assump_15
    intro assump_16
    apply True.intro
  let assump_4 := assump_1 assump_21
  have assump_23 : (((p2 ∨ True) ∨ (p7 ∧ p7)) ∨ ((p1 ∨ p6) ∧ (p2 → p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_17 := assump_4 assump_23
  apply False.elim assump_17


variable (p1 p3 p4 p2 p5 p7 : Prop)
theorem file38_99987 : (((((p3 ∨ p7) ∧ (False → False)) → False) → (((p5 ∧ p7) ∧ (p3 → False)) → False)) ∧ ((((False ∨ p4) → (True → p4)) → False) → (((p1 → p5) ∧ (p2 → False)) ∧ ((p5 → p1) ∨ (p5 ∧ p7))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_81 : ((p3 ∨ p7) ∧ (False → False)) := by
        apply And.intro
        apply Or.inr
        exact assump_6
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_1 assump_81
      apply False.elim assump_15
  intro assump_22
  apply And.intro
  apply And.intro
  intro assump_23
  have assump_82 : ((False ∨ p4) → (True → p4)) := by
    intro assump_29
    intro assump_30
    cases assump_29
    case inl assump_33 =>
      apply False.elim assump_33
    case inr assump_34 =>
      exact assump_34
  let assump_28 := assump_22 assump_82
  apply False.elim assump_28
  intro assump_42
  have assump_83 : ((False ∨ p4) → (True → p4)) := by
    intro assump_48
    intro assump_49
    cases assump_48
    case inl assump_52 =>
      apply False.elim assump_52
    case inr assump_53 =>
      exact assump_53
  let assump_47 := assump_22 assump_83
  apply False.elim assump_47
  apply Or.inl
  intro assump_63
  have assump_84 : ((False ∨ p4) → (True → p4)) := by
    intro assump_68
    intro assump_69
    cases assump_68
    case inl assump_72 =>
      apply False.elim assump_72
    case inr assump_73 =>
      exact assump_73
  let assump_67 := assump_22 assump_84
  apply False.elim assump_67


variable (p4 p2 p1 p5 p0 p3 : Prop)
theorem file38_101645 : (((((p5 → p1) ∧ (p0 → False)) → False) → False) → ((((p5 ∨ p2) ∧ (p3 ∨ False)) → False) → (((False ∧ p2) → False) ∨ ((p4 → p0) ∨ (p3 → p2))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p1 p2 p0 p6 p3 p7 p5 : Prop)
theorem file38_102004 : ((((((p6 ∧ p0) ∧ (p7 ∨ False)) ∧ ((p3 ∨ p3) → False)) ∧ (((p2 → p5) ∧ (p6 ∨ True)) ∧ ((p2 → False) → (p3 → False)))) ∧ ((((p5 ∧ p1) ∨ (False → False)) → ((p1 → False) ∧ (p1 → False))) ∧ (((p7 ∨ p3) ∨ (p3 → False)) → False))) → False) := by
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
              cases assump_5
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case inl assump_28 =>
                    cases assump_3
                    case intro assump_34 assump_35 =>
                      have assump_60 : ((p7 ∨ p3) ∨ (p3 → False)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_16
                      let assump_40 := assump_35 assump_60
                      apply False.elim assump_40
                  case inr assump_29 =>
                    cases assump_3
                    case intro assump_48 assump_49 =>
                      have assump_61 : ((p7 ∨ p3) ∨ (p3 → False)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_16
                      let assump_54 := assump_49 assump_61
                      apply False.elim assump_54
            case inr assump_17 =>
              apply False.elim assump_17


variable (p3 p0 p6 p5 p2 p1 : Prop)
theorem file38_103793 : (((((True → False) ∧ (p2 → True)) → False) ∧ (((p1 ∨ p0) ∧ (p3 → p5)) → ((p6 ∨ p1) → (p3 → p1)))) → ((((p1 → p1) ∧ (p2 ∨ p5)) ∨ ((p5 ∨ p3) ∨ (p6 ∨ p1))) ∨ (((p1 ∧ p2) ∧ (p2 → False)) → ((p5 ∨ p5) → (p5 ∨ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_11
    intro assump_12
    cases assump_12
    case inl assump_13 =>
      cases assump_11
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          apply Or.inl
          exact assump_13
    case inr assump_14 =>
      cases assump_11
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          apply Or.inl
          exact assump_14


variable (p1 p0 p6 p5 p2 p7 : Prop)
theorem file38_104622 : (((((p5 → p5) ∨ (p1 ∨ p1)) ∧ ((p7 → p7) ∧ (p0 → False))) → False) → ((((p6 → p6) ∨ (p6 ∧ True)) ∨ ((False ∧ p6) → False)) ∨ (((p0 ∧ p1) ∧ (p5 ∧ p2)) → ((p5 ∧ True) → False)))) := by
  intro assump_14
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_17
  exact assump_17


variable (p3 p6 p5 p0 p2 : Prop)
theorem file38_104960 : ((((((p3 ∨ p3) ∧ (p3 → False)) ∧ ((p6 ∨ p2) ∨ (p3 ∨ p3))) → False) ∧ ((((True → p5) → (p3 → p6)) → ((p2 → True) ∧ (p0 → False))) ∧ (((False ∨ True) ∨ (p6 ∧ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : ((False ∨ True) ∨ (p6 ∧ p3)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p5 p0 p3 p4 : Prop)
theorem file38_105524 : (((((p4 → p4) ∨ (False ∨ p0)) ∨ ((p3 → p5) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : (((p4 → p4) ∨ (False ∨ p0)) ∨ ((p3 → p5) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p4 p3 p1 p2 p7 p0 : Prop)
theorem file38_105894 : (((((p0 ∨ p3) ∧ (p1 ∧ False)) ∨ ((False ∧ p3) → (p3 ∨ p2))) ∨ (((p4 ∧ p7) → False) → False)) ∨ ((((p7 ∧ False) → (p5 ∧ p5)) → ((p2 ∧ p1) → (p4 → p3))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p4 p5 p7 p3 p1 p6 p2 p0 : Prop)
theorem file38_106270 : (((((p2 ∧ p4) → (p0 → p0)) → False) → False) ∨ ((((False → p2) → (p5 ∧ p3)) ∨ ((p4 → False) ∧ (p6 → False))) → (((p6 ∨ p7) ∨ (p4 → p5)) ∨ ((p1 ∨ p4) → (p5 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p2 ∧ p4) → (p0 → p0)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p4 p6 p7 p0 p5 : Prop)
theorem file38_106762 : ((((((p0 ∨ p2) ∨ (p4 ∧ p7)) → False) → (((p2 ∧ p6) → False) ∨ ((p5 → p2) → False))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p0 ∨ p2) ∨ (p4 ∧ p7)) → False) → (((p2 ∧ p6) → False) ∨ ((p5 → p2) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_25 : ((p0 ∨ p2) ∨ (p4 ∧ p7)) := by
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_17 := assump_5 assump_25
      apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p3 p5 p7 p2 p4 p1 p0 p6 : Prop)
theorem file38_107429 : (((((p7 ∧ False) → False) → False) ∨ (((p3 ∨ p2) → (p3 ∧ True)) ∧ ((False → p1) → (True → False)))) → ((((p5 ∧ p5) ∨ (p5 → p7)) ∨ ((p4 ∨ p5) → False)) → (((p7 ∧ p6) → (p0 → False)) ∧ ((p6 → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_2
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_1
          case inl assump_23 =>
            have assump_218 : ((p7 ∧ False) → False) := by
              intro assump_28
              cases assump_28
              case intro assump_29 assump_30 =>
                apply False.elim assump_30
            let assump_27 := assump_23 assump_218
            apply False.elim assump_27
          case inr assump_24 =>
            cases assump_24
            case intro assump_38 assump_39 =>
              have assump_219 : (False → p1) := by
                intro assump_45
                apply False.elim assump_45
              let assump_44 := assump_39 assump_219
              have assump_220 : True := by
                apply True.intro
              let assump_48 := assump_44 assump_220
              apply False.elim assump_48
      case inr assump_16 =>
        cases assump_1
        case inl assump_54 =>
          have assump_221 : ((p7 ∧ False) → False) := by
            intro assump_59
            cases assump_59
            case intro assump_60 assump_61 =>
              apply False.elim assump_61
          let assump_58 := assump_54 assump_221
          apply False.elim assump_58
        case inr assump_55 =>
          cases assump_55
          case intro assump_69 assump_70 =>
            have assump_222 : (False → p1) := by
              intro assump_76
              apply False.elim assump_76
            let assump_75 := assump_70 assump_222
            have assump_223 : True := by
              apply True.intro
            let assump_79 := assump_75 assump_223
            apply False.elim assump_79
    case inr assump_14 =>
      cases assump_1
      case inl assump_85 =>
        have assump_224 : ((p7 ∧ False) → False) := by
          intro assump_90
          cases assump_90
          case intro assump_91 assump_92 =>
            apply False.elim assump_92
        let assump_89 := assump_85 assump_224
        apply False.elim assump_89
      case inr assump_86 =>
        cases assump_86
        case intro assump_100 assump_101 =>
          have assump_225 : (False → p1) := by
            intro assump_107
            apply False.elim assump_107
          let assump_106 := assump_101 assump_225
          have assump_226 : True := by
            apply True.intro
          let assump_110 := assump_106 assump_226
          apply False.elim assump_110
  intro assump_114
  cases assump_2
  case inl assump_117 =>
    cases assump_117
    case inl assump_119 =>
      cases assump_119
      case intro assump_121 assump_122 =>
        cases assump_1
        case inl assump_127 =>
          have assump_227 : ((p7 ∧ False) → False) := by
            intro assump_132
            cases assump_132
            case intro assump_133 assump_134 =>
              apply False.elim assump_134
          let assump_131 := assump_127 assump_227
          apply False.elim assump_131
        case inr assump_128 =>
          cases assump_128
          case intro assump_142 assump_143 =>
            have assump_228 : (False → p1) := by
              intro assump_149
              apply False.elim assump_149
            let assump_148 := assump_143 assump_228
            have assump_229 : True := by
              apply True.intro
            let assump_152 := assump_148 assump_229
            apply False.elim assump_152
    case inr assump_120 =>
      cases assump_1
      case inl assump_158 =>
        have assump_230 : ((p7 ∧ False) → False) := by
          intro assump_163
          cases assump_163
          case intro assump_164 assump_165 =>
            apply False.elim assump_165
        let assump_162 := assump_158 assump_230
        apply False.elim assump_162
      case inr assump_159 =>
        cases assump_159
        case intro assump_173 assump_174 =>
          have assump_231 : (False → p1) := by
            intro assump_180
            apply False.elim assump_180
          let assump_179 := assump_174 assump_231
          have assump_232 : True := by
            apply True.intro
          let assump_183 := assump_179 assump_232
          apply False.elim assump_183
  case inr assump_118 =>
    cases assump_1
    case inl assump_189 =>
      have assump_233 : ((p7 ∧ False) → False) := by
        intro assump_194
        cases assump_194
        case intro assump_195 assump_196 =>
          apply False.elim assump_196
      let assump_193 := assump_189 assump_233
      apply False.elim assump_193
    case inr assump_190 =>
      cases assump_190
      case intro assump_204 assump_205 =>
        have assump_234 : (False → p1) := by
          intro assump_211
          apply False.elim assump_211
        let assump_210 := assump_205 assump_234
        have assump_235 : True := by
          apply True.intro
        let assump_214 := assump_210 assump_235
        apply False.elim assump_214


variable (p1 p0 p4 p3 p6 : Prop)
theorem file38_112842 : (((((p1 ∨ p1) ∨ (False → False)) → False) → False) ∧ ((((True ∨ p6) → False) ∨ ((p3 → False) ∧ (p0 ∧ p4))) → (((p1 → p6) ∧ (False ∧ p0)) → False))) := by
  apply And.intro
  intro assump_1
  have assump_21 : ((p1 ∨ p1) ∨ (False → False)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4
  intro assump_11
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      apply False.elim assump_17


variable (p2 p1 p7 p4 p3 p5 p6 p0 : Prop)
theorem file38_113464 : (((((False → False) ∨ (p1 ∨ p3)) ∧ ((p4 → p4) ∧ (p1 → False))) → (((p5 ∧ p1) ∧ (False ∧ p0)) → ((p6 ∨ p3) ∨ (p2 ∧ p3)))) ∨ ((((p3 ∧ p5) → (p2 ∨ p2)) ∧ ((p5 ∧ p5) ∧ (p2 → False))) → (((p7 ∨ p7) → (p1 → p3)) ∨ ((p1 → False) → (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        apply False.elim assump_11


variable (p3 p6 p5 p0 p1 p2 p4 : Prop)
theorem file38_114025 : (((((p3 → False) → False) ∨ ((p2 ∨ p4) ∧ (p6 ∧ p1))) → False) → ((((True ∨ p0) ∨ (p5 ∨ p5)) ∨ ((p4 → False) → False)) ∨ (((p1 → False) → (p4 ∧ True)) ∨ ((p2 ∧ p2) ∧ (p1 → p3))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p4 p1 p2 p6 p7 p3 : Prop)
theorem file38_114366 : (((((p3 ∨ p4) ∧ (False ∧ False)) ∧ ((True ∨ p4) ∧ (p6 ∧ False))) ∧ (((p7 → p4) ∧ (False ∨ p3)) → ((p2 → False) ∨ (False → p1)))) → False) := by
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
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
        case inr assump_9 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            apply False.elim assump_18


variable (p6 p5 p3 p4 p1 : Prop)
theorem file38_115046 : ((((((False ∨ p5) ∨ (p1 ∧ p1)) → ((p3 ∧ p5) → (p6 → p6))) → False) ∨ ((((False → False) → False) → ((p6 → p4) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_54 : (((False ∨ p5) ∨ (p1 ∧ p1)) → ((p3 ∧ p5) → (p6 → p6))) := by
      intro assump_7
      intro assump_8
      intro assump_9
      cases assump_8
      case intro assump_12 assump_13 =>
        cases assump_7
        case inl assump_18 =>
          cases assump_18
          case inl assump_20 =>
            apply False.elim assump_20
          case inr assump_21 =>
            exact assump_9
        case inr assump_19 =>
          cases assump_19
          case intro assump_26 assump_27 =>
            exact assump_9
    let assump_6 := assump_2 assump_54
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_55 : (((False → False) → False) → ((p6 → p4) → False)) := by
      intro assump_38
      intro assump_39
      have assump_56 : (False → False) := by
        intro assump_45
        apply False.elim assump_45
      let assump_44 := assump_38 assump_56
      apply False.elim assump_44
    let assump_37 := assump_3 assump_55
    apply False.elim assump_37


variable (p0 p3 p5 p1 p2 p4 p6 p7 : Prop)
theorem file38_116320 : (((((p2 ∧ p2) ∧ (p5 → False)) ∧ ((p1 → False) ∧ (True → False))) → (((p6 → p2) → (p4 → False)) ∧ ((p0 → False) ∧ (p3 ∨ False)))) → ((((True ∨ p7) ∧ (p2 → False)) → ((p4 ∧ p2) → False)) ∨ (((p4 ∨ p2) → (True → False)) → ((p5 ∨ p3) → (True ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        have assump_32 : p2 := by
          exact assump_7
        let assump_20 := assump_13 assump_32
        apply False.elim assump_20
      case inr assump_15 =>
        have assump_33 : p2 := by
          exact assump_7
        let assump_28 := assump_13 assump_33
        apply False.elim assump_28


variable (p6 p1 p0 p5 p2 p3 : Prop)
theorem file38_117164 : ((((((p2 ∧ p3) ∨ (p1 → True)) → False) → (((p1 → p0) → (p2 → p6)) ∨ ((p5 ∨ p1) ∨ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p2 ∧ p3) ∨ (p1 → True)) → False) → (((p1 → p0) → (p2 → p6)) ∨ ((p5 ∨ p1) ∨ (p1 → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_25 : ((p2 ∧ p3) ∨ (p1 → True)) := by
      apply Or.inr
      intro assump_17
      apply True.intro
    let assump_16 := assump_5 assump_25
    apply False.elim assump_16
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p4 p2 p0 p5 p3 p6 : Prop)
theorem file38_117809 : (((((False → False) ∨ (True → p4)) → False) → False) ∨ ((((p5 → False) ∨ (p3 ∧ p6)) → ((p6 ∧ p5) ∨ (p3 ∨ p0))) → (((p2 ∧ True) → (p2 → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (True → p4)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p0 p6 p2 p3 : Prop)
theorem file38_118243 : (((((False → False) → False) ∨ ((p2 → p6) → False)) → (((False ∨ False) ∧ (p4 ∨ p2)) → ((p4 → p3) ∨ (True → False)))) ∨ ((((p3 ∨ True) → (p3 ∧ p6)) → False) ∧ (((p0 → p4) → False) ∨ ((True → False) ∧ (p0 ∧ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      apply False.elim assump_6


variable (p3 p2 p1 : Prop)
theorem file38_118747 : ((((((p1 → True) → (p3 ∨ p2)) ∧ ((p2 → True) → False)) → False) → False) → False) := by
  intro assump_7
  have assump_26 : ((((p1 → True) → (p3 ∨ p2)) ∧ ((p2 → True) → False)) → False) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      have assump_27 : (p2 → True) := by
        intro assump_19
        apply True.intro
      let assump_18 := assump_13 assump_27
      apply False.elim assump_18
  let assump_10 := assump_7 assump_26
  apply False.elim assump_10


variable (p5 p6 p7 p2 p1 p4 p0 : Prop)
theorem file38_119313 : ((((((p6 ∨ p7) → (p4 ∨ p4)) → ((True → False) → (p2 ∧ p4))) ∨ (((p2 ∧ p0) → (False ∧ p0)) ∨ ((p1 → p5) → False))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p6 ∨ p7) → (p4 ∨ p4)) → ((True → False) → (p2 ∧ p4))) ∨ (((p2 ∧ p0) → (False ∧ p0)) ∨ ((p1 → p5) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    have assump_29 : True := by
      apply True.intro
    let assump_12 := assump_6 assump_29
    apply False.elim assump_12
    have assump_30 : True := by
      apply True.intro
    let assump_21 := assump_6 assump_30
    apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p1 p4 p7 p0 : Prop)
theorem file38_120051 : ((((((p4 ∨ p7) → (p0 → False)) ∧ ((p0 ∧ p4) ∧ (p1 → p4))) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p4 ∨ p7) → (p0 → False)) ∧ ((p0 ∧ p4) ∧ (p1 → p4))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_32 : (p4 ∨ p7) := by
            apply Or.inl
            exact assump_13
          let assump_23 := assump_6 assump_32
          have assump_33 : p0 := by
            exact assump_12
          let assump_24 := assump_23 assump_33
          apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p2 p7 p4 p0 p5 : Prop)
theorem file38_120862 : (((((p7 → p4) ∧ (p5 ∨ False)) ∧ ((p4 ∧ p5) → (p7 → False))) ∧ (((p2 → p4) ∧ (True → False)) ∨ ((False ∧ p2) ∧ (False → p0)))) → False) := by
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
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_36 : True := by
                apply True.intro
              let assump_24 := assump_19 assump_36
              apply False.elim assump_24
          case inr assump_17 =>
            cases assump_17
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                apply False.elim assump_30
        case inr assump_11 =>
          apply False.elim assump_11


variable (p7 p5 p0 p1 p6 p3 : Prop)
theorem file38_121890 : ((((((p5 → True) → False) ∧ ((p3 ∨ p3) → False)) ∧ (((p5 ∧ p5) ∨ (False → p1)) → False)) ∨ ((((p6 → False) → (False → False)) ∨ ((p1 → False) → (p7 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_31 : ((p5 ∧ p5) ∨ (False → p1)) := by
          apply Or.inr
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_5 assump_31
        apply False.elim assump_14
  case inr assump_3 =>
    have assump_32 : (((p6 → False) → (False → False)) ∨ ((p1 → False) → (p7 ∧ p0))) := by
      apply Or.inl
      intro assump_24
      intro assump_25
      apply False.elim assump_25
    let assump_23 := assump_3 assump_32
    apply False.elim assump_23


variable (p2 p3 p6 p1 p5 p7 : Prop)
theorem file38_122806 : (((((False → p1) → (p1 → False)) ∨ ((p5 → p6) ∧ (False ∧ p5))) → (((p5 ∧ p3) → (True ∨ p6)) → ((p1 → False) ∧ (p1 → False)))) ∨ ((((p1 → p1) → False) → ((p2 ∧ p7) ∧ (p6 → True))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    have assump_53 : (False → p1) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_8 assump_53
    have assump_54 : p1 := by
      exact assump_3
    let assump_16 := assump_12 assump_54
    apply False.elim assump_16
  case inr assump_9 =>
    cases assump_9
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  intro assump_28
  cases assump_1
  case inl assump_33 =>
    have assump_55 : (False → p1) := by
      intro assump_38
      apply False.elim assump_38
    let assump_37 := assump_33 assump_55
    have assump_56 : p1 := by
      exact assump_28
    let assump_41 := assump_37 assump_56
    apply False.elim assump_41
  case inr assump_34 =>
    cases assump_34
    case intro assump_45 assump_46 =>
      cases assump_46
      case intro assump_49 assump_50 =>
        apply False.elim assump_49


variable (p0 p1 : Prop)
theorem file38_124106 : (((((False → p1) → False) → False) → False) → ((((True → False) → (p0 → p1)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_21 : (((False → p1) → False) → False) := by
    intro assump_8
    have assump_22 : (False → p1) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_8 assump_22
    apply False.elim assump_11
  let assump_7 := assump_1 assump_21
  apply False.elim assump_7


variable (p2 p3 p5 p0 p1 : Prop)
theorem file38_124607 : ((((((p0 ∨ p5) ∧ (p2 → False)) ∧ ((False ∧ False) ∧ (True → True))) → False) → ((((p0 → p3) → False) → ((p3 → False) ∨ (p2 ∨ p1))) → False)) → False) := by
  intro assump_20
  have assump_69 : ((((p0 ∨ p5) ∧ (p2 → False)) ∧ ((False ∧ False) ∧ (True → True))) → False) := by
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_27
        case inl assump_29 =>
          cases assump_26
          case intro assump_35 assump_36 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
        case inr assump_30 =>
          cases assump_26
          case intro assump_45 assump_46 =>
            cases assump_45
            case intro assump_47 assump_48 =>
              apply False.elim assump_47
  let assump_23 := assump_20 assump_69
  have assump_70 : (((p0 → p3) → False) → ((p3 → False) ∨ (p2 ∨ p1))) := by
    intro assump_52
    apply Or.inl
    intro assump_55
    have assump_71 : (p0 → p3) := by
      intro assump_60
      exact assump_55
    let assump_59 := assump_52 assump_71
    apply False.elim assump_59
  let assump_51 := assump_23 assump_70
  apply False.elim assump_51


variable (p4 p6 p3 p1 p2 p0 p5 : Prop)
theorem file38_125931 : ((((((p0 → p1) → (p4 ∧ p2)) ∧ ((False → p3) → False)) ∧ (((False ∨ False) ∧ (p4 → p0)) ∧ ((p5 → p6) ∨ (False → False)))) ∧ ((((p3 ∨ p1) ∨ (p2 → p1)) → False) ∧ (((p5 ∧ p2) → (p4 → False)) → False))) → False) := by
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
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              apply False.elim assump_17


variable (p3 p4 p5 p1 p7 p0 : Prop)
theorem file38_126700 : ((((((p4 → p5) → (p1 ∨ True)) ∧ ((False → True) → False)) → False) ∧ ((((p0 → False) ∨ (p3 → p4)) → False) ∧ (((p7 ∨ False) ∨ (False ∧ p4)) ∧ ((p5 → p7) → False)))) → False) := by
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
            have assump_33 : (p5 → p7) := by
              intro assump_21
              exact assump_14
            let assump_20 := assump_11 assump_33
            apply False.elim assump_20
          case inr assump_15 =>
            apply False.elim assump_15
        case inr assump_13 =>
          cases assump_13
          case intro assump_29 assump_30 =>
            apply False.elim assump_29


variable (p0 p6 p3 : Prop)
theorem file38_127630 : (((((p3 ∨ p6) → False) → ((p0 → False) → (True ∨ False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p3 ∨ p6) → False) → ((p0 → False) → (True ∨ False))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p6 p7 p0 p4 p1 p3 : Prop)
theorem file38_128014 : ((((((p3 ∧ p1) ∧ (p6 ∨ p7)) ∧ ((p0 ∧ p0) → False)) → (((p5 → False) → False) → ((p4 ∨ p1) ∨ (p0 → p6)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p3 ∧ p1) ∧ (p6 ∨ p7)) ∧ ((p0 ∧ p0) → False)) → (((p5 → False) → False) → ((p4 ∨ p1) ∨ (p0 → p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case inl assump_19 =>
            apply Or.inl
            apply Or.inr
            exact assump_14
          case inr assump_20 =>
            apply Or.inl
            apply Or.inr
            exact assump_14
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


