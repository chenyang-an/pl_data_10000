variable (p4 p3 p0 p1 p6 p2 : Prop)
theorem file1_44 : (((((p1 → False) → (p1 → False)) ∨ ((p0 → p4) → (p1 → False))) → False) → ((((True → False) → (p6 → False)) → ((False → p6) → (p3 → False))) → (((p1 ∧ False) ∧ (False → False)) → ((p4 ∧ p4) ∧ (p2 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  cases assump_3
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      apply False.elim assump_15
  apply And.intro
  cases assump_3
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      apply False.elim assump_23
  cases assump_3
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      apply False.elim assump_31


variable (p5 p1 p7 p6 p2 p4 p0 : Prop)
theorem file1_994 : (((((p6 → p2) → False) → ((p0 ∧ p5) → (p0 ∨ p7))) ∨ (((p0 ∨ False) → (p5 → False)) ∨ ((p7 ∨ p4) → False))) ∨ ((((p2 → p4) → False) → False) ∧ (((p1 → False) → (p2 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_16
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    apply Or.inl
    exact assump_18


variable (p2 p6 p7 p1 p3 p0 : Prop)
theorem file1_1401 : (((((p3 → p0) ∨ (p6 → p1)) ∨ ((p6 ∨ p2) → (p2 ∧ p6))) ∨ (((True → False) ∨ (p6 → False)) ∧ ((p2 → False) ∧ (p3 → False)))) → ((((p7 → False) → (p2 → True)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_73 : ((p7 → False) → (p2 → True)) := by
          intro assump_15
          intro assump_16
          apply True.intro
        let assump_14 := assump_2 assump_73
        apply False.elim assump_14
      case inr assump_10 =>
        have assump_74 : ((p7 → False) → (p2 → True)) := by
          intro assump_24
          intro assump_25
          apply True.intro
        let assump_23 := assump_2 assump_74
        apply False.elim assump_23
    case inr assump_8 =>
      have assump_75 : ((p7 → False) → (p2 → True)) := by
        intro assump_33
        intro assump_34
        apply True.intro
      let assump_32 := assump_2 assump_75
      apply False.elim assump_32
  case inr assump_6 =>
    cases assump_6
    case intro assump_38 assump_39 =>
      cases assump_38
      case inl assump_40 =>
        cases assump_39
        case intro assump_44 assump_45 =>
          have assump_76 : True := by
            apply True.intro
          let assump_52 := assump_40 assump_76
          apply False.elim assump_52
      case inr assump_41 =>
        cases assump_39
        case intro assump_58 assump_59 =>
          have assump_77 : ((p7 → False) → (p2 → True)) := by
            intro assump_68
            intro assump_69
            apply True.intro
          let assump_67 := assump_2 assump_77
          apply False.elim assump_67


variable (p1 p5 p6 p2 p0 p7 : Prop)
theorem file1_3174 : ((((((p5 ∨ p6) → (True → p0)) ∧ ((p1 ∧ p0) ∧ (True ∧ False))) ∧ (((p6 ∧ True) ∨ (p5 → p6)) ∧ ((p1 ∧ True) → (p6 ∧ p7)))) ∧ ((((p5 ∨ p0) → False) ∧ ((p6 ∨ False) → False)) → (((True → p1) ∧ (p1 → False)) ∨ ((p2 → False) ∧ (False ∨ p2))))) → False) := by
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_29
        case intro assump_32 assump_33 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            cases assump_33
            case intro assump_40 assump_41 =>
              apply False.elim assump_41


variable (p2 p5 p3 p0 p4 p6 : Prop)
theorem file1_3930 : ((((((p6 ∨ p3) → (p3 ∧ True)) → ((True ∨ p4) ∨ (True → p0))) ∨ (((p2 ∧ p3) ∨ (True → p5)) → False)) → False) → False) := by
  intro assump_10
  have assump_20 : ((((p6 ∨ p3) → (p3 ∧ True)) → ((True ∨ p4) ∨ (True → p0))) ∨ (((p2 ∧ p3) ∨ (True → p5)) → False)) := by
    apply Or.inl
    intro assump_14
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_13 := assump_10 assump_20
  apply False.elim assump_13


variable (p2 p3 p5 p4 p6 p7 p1 : Prop)
theorem file1_4418 : (((((p4 → True) → (p2 ∧ False)) → ((p6 ∧ True) ∨ (p1 ∨ p1))) ∨ (((p7 ∧ p1) → False) → ((p6 → False) ∨ (False ∧ p7)))) ∨ ((((p3 ∨ p5) ∨ (p6 ∧ p6)) → ((p6 → p6) ∧ (p7 → p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (p4 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_11
  let assump_6 := And.right assump_4
  apply False.elim assump_6


variable (p2 : Prop)
theorem file1_4878 : ((((((True ∨ True) → False) ∧ ((p2 → False) ∨ (False ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((True ∨ True) → False) ∧ ((p2 → False) ∨ (False ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_27 : (True ∨ True) := by
          apply Or.inl
          apply True.intro
        let assump_15 := assump_6 assump_27
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_19 assump_20 =>
          apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p6 p4 p1 p3 p0 : Prop)
theorem file1_5641 : (((((p6 → False) ∨ (p0 ∧ p0)) ∨ ((p5 ∧ p1) ∨ (True → True))) → (((p3 ∧ p1) ∧ (p0 ∧ p6)) → ((False → False) ∨ (False → False)))) ∧ ((((p6 → False) ∧ (p1 ∧ p1)) ∧ ((p3 ∨ p3) → False)) → (((p3 → p6) → False) → ((p0 → False) ∨ (p4 → False))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_1
        case inl assump_17 =>
          cases assump_17
          case inl assump_19 =>
            apply Or.inl
            intro assump_23
            apply False.elim assump_23
          case inr assump_20 =>
            cases assump_20
            case intro assump_26 assump_27 =>
              apply Or.inl
              intro assump_32
              apply False.elim assump_32
        case inr assump_18 =>
          cases assump_18
          case inl assump_35 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              apply Or.inl
              intro assump_43
              apply False.elim assump_43
          case inr assump_36 =>
            apply Or.inl
            intro assump_48
            apply False.elim assump_48
  intro assump_51
  intro assump_52
  cases assump_51
  case intro assump_55 assump_56 =>
    cases assump_55
    case intro assump_57 assump_58 =>
      cases assump_58
      case intro assump_61 assump_62 =>
        apply Or.inl
        intro assump_69
        have assump_90 : (p3 → p6) := by
          intro assump_78
          have assump_91 : (p3 ∨ p3) := by
            apply Or.inl
            exact assump_78
          let assump_83 := assump_56 assump_91
          apply False.elim assump_83
        let assump_77 := assump_52 assump_90
        apply False.elim assump_77


variable (p0 p5 p1 p7 p4 p6 p2 p3 : Prop)
theorem file1_7545 : (((((p0 ∧ p0) → (p7 → False)) ∧ ((p5 ∨ p2) ∧ (p1 → False))) → (((p2 ∧ p3) → False) → ((p0 ∧ False) ∨ (p4 → p4)))) ∨ ((((p2 ∨ p5) → False) ∧ ((p1 ∧ p5) ∨ (p7 → False))) ∧ (((p7 ∨ p3) → False) ∧ ((p4 → False) ∧ (p0 ∧ p6))))) := by
  apply Or.inl
  intro assump_24
  intro assump_25
  cases assump_24
  case intro assump_28 assump_29 =>
    cases assump_29
    case intro assump_32 assump_33 =>
      cases assump_32
      case inl assump_34 =>
        apply Or.inr
        intro assump_40
        exact assump_40
      case inr assump_35 =>
        apply Or.inr
        intro assump_47
        exact assump_47


variable (p0 p1 p4 p5 p7 : Prop)
theorem file1_8210 : ((((((p5 ∧ p0) ∧ (True → p7)) → ((p4 → p0) ∨ (False ∨ p1))) → (((p7 ∨ True) ∨ (True ∨ True)) ∨ ((p4 ∨ p4) → (p4 → p7)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 ∧ p0) ∧ (True → p7)) → ((p4 → p0) ∨ (False ∨ p1))) → (((p7 ∨ True) ∨ (True ∨ True)) ∨ ((p4 ∨ p4) → (p4 → p7)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p0 p4 p1 p7 p2 p5 : Prop)
theorem file1_8735 : (((((False → False) → False) → False) → False) → ((((False → False) → (p2 ∨ p7)) ∨ ((p5 → False) ∧ (p0 ∧ p1))) → (((p7 ∨ p5) ∧ (p4 ∨ p0)) → ((p4 ∨ p6) → (p7 → p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_3
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_13
        case inl assump_18 =>
          cases assump_2
          case inl assump_22 =>
            have assump_422 : (((False → False) → False) → False) := by
              intro assump_29
              have assump_423 : (False → False) := by
                intro assump_33
                apply False.elim assump_33
              let assump_32 := assump_29 assump_423
              apply False.elim assump_32
            let assump_28 := assump_1 assump_422
            apply False.elim assump_28
          case inr assump_23 =>
            cases assump_23
            case intro assump_42 assump_43 =>
              cases assump_43
              case intro assump_46 assump_47 =>
                have assump_424 : (((False → False) → False) → False) := by
                  intro assump_55
                  have assump_425 : (False → False) := by
                    intro assump_59
                    apply False.elim assump_59
                  let assump_58 := assump_55 assump_425
                  apply False.elim assump_58
                let assump_54 := assump_1 assump_424
                apply False.elim assump_54
        case inr assump_19 =>
          cases assump_2
          case inl assump_70 =>
            have assump_426 : (((False → False) → False) → False) := by
              intro assump_77
              have assump_427 : (False → False) := by
                intro assump_81
                apply False.elim assump_81
              let assump_80 := assump_77 assump_427
              apply False.elim assump_80
            let assump_76 := assump_1 assump_426
            apply False.elim assump_76
          case inr assump_71 =>
            cases assump_71
            case intro assump_90 assump_91 =>
              cases assump_91
              case intro assump_94 assump_95 =>
                have assump_428 : (((False → False) → False) → False) := by
                  intro assump_103
                  have assump_429 : (False → False) := by
                    intro assump_107
                    apply False.elim assump_107
                  let assump_106 := assump_103 assump_429
                  apply False.elim assump_106
                let assump_102 := assump_1 assump_428
                apply False.elim assump_102
      case inr assump_15 =>
        cases assump_13
        case inl assump_118 =>
          cases assump_2
          case inl assump_122 =>
            have assump_430 : (((False → False) → False) → False) := by
              intro assump_129
              have assump_431 : (False → False) := by
                intro assump_133
                apply False.elim assump_133
              let assump_132 := assump_129 assump_431
              apply False.elim assump_132
            let assump_128 := assump_1 assump_430
            apply False.elim assump_128
          case inr assump_123 =>
            cases assump_123
            case intro assump_142 assump_143 =>
              cases assump_143
              case intro assump_146 assump_147 =>
                have assump_432 : (((False → False) → False) → False) := by
                  intro assump_155
                  have assump_433 : (False → False) := by
                    intro assump_159
                    apply False.elim assump_159
                  let assump_158 := assump_155 assump_433
                  apply False.elim assump_158
                let assump_154 := assump_1 assump_432
                apply False.elim assump_154
        case inr assump_119 =>
          cases assump_2
          case inl assump_170 =>
            have assump_434 : (((False → False) → False) → False) := by
              intro assump_177
              have assump_435 : (False → False) := by
                intro assump_181
                apply False.elim assump_181
              let assump_180 := assump_177 assump_435
              apply False.elim assump_180
            let assump_176 := assump_1 assump_434
            apply False.elim assump_176
          case inr assump_171 =>
            cases assump_171
            case intro assump_190 assump_191 =>
              cases assump_191
              case intro assump_194 assump_195 =>
                have assump_436 : (((False → False) → False) → False) := by
                  intro assump_203
                  have assump_437 : (False → False) := by
                    intro assump_207
                    apply False.elim assump_207
                  let assump_206 := assump_203 assump_437
                  apply False.elim assump_206
                let assump_202 := assump_1 assump_436
                apply False.elim assump_202
  case inr assump_9 =>
    cases assump_3
    case intro assump_218 assump_219 =>
      cases assump_218
      case inl assump_220 =>
        cases assump_219
        case inl assump_224 =>
          cases assump_2
          case inl assump_228 =>
            have assump_438 : (((False → False) → False) → False) := by
              intro assump_235
              have assump_439 : (False → False) := by
                intro assump_239
                apply False.elim assump_239
              let assump_238 := assump_235 assump_439
              apply False.elim assump_238
            let assump_234 := assump_1 assump_438
            apply False.elim assump_234
          case inr assump_229 =>
            cases assump_229
            case intro assump_248 assump_249 =>
              cases assump_249
              case intro assump_252 assump_253 =>
                have assump_440 : (((False → False) → False) → False) := by
                  intro assump_261
                  have assump_441 : (False → False) := by
                    intro assump_265
                    apply False.elim assump_265
                  let assump_264 := assump_261 assump_441
                  apply False.elim assump_264
                let assump_260 := assump_1 assump_440
                apply False.elim assump_260
        case inr assump_225 =>
          cases assump_2
          case inl assump_276 =>
            have assump_442 : (((False → False) → False) → False) := by
              intro assump_283
              have assump_443 : (False → False) := by
                intro assump_287
                apply False.elim assump_287
              let assump_286 := assump_283 assump_443
              apply False.elim assump_286
            let assump_282 := assump_1 assump_442
            apply False.elim assump_282
          case inr assump_277 =>
            cases assump_277
            case intro assump_296 assump_297 =>
              cases assump_297
              case intro assump_300 assump_301 =>
                have assump_444 : (((False → False) → False) → False) := by
                  intro assump_309
                  have assump_445 : (False → False) := by
                    intro assump_313
                    apply False.elim assump_313
                  let assump_312 := assump_309 assump_445
                  apply False.elim assump_312
                let assump_308 := assump_1 assump_444
                apply False.elim assump_308
      case inr assump_221 =>
        cases assump_219
        case inl assump_324 =>
          cases assump_2
          case inl assump_328 =>
            have assump_446 : (((False → False) → False) → False) := by
              intro assump_335
              have assump_447 : (False → False) := by
                intro assump_339
                apply False.elim assump_339
              let assump_338 := assump_335 assump_447
              apply False.elim assump_338
            let assump_334 := assump_1 assump_446
            apply False.elim assump_334
          case inr assump_329 =>
            cases assump_329
            case intro assump_348 assump_349 =>
              cases assump_349
              case intro assump_352 assump_353 =>
                have assump_448 : (((False → False) → False) → False) := by
                  intro assump_361
                  have assump_449 : (False → False) := by
                    intro assump_365
                    apply False.elim assump_365
                  let assump_364 := assump_361 assump_449
                  apply False.elim assump_364
                let assump_360 := assump_1 assump_448
                apply False.elim assump_360
        case inr assump_325 =>
          cases assump_2
          case inl assump_376 =>
            have assump_450 : (((False → False) → False) → False) := by
              intro assump_383
              have assump_451 : (False → False) := by
                intro assump_387
                apply False.elim assump_387
              let assump_386 := assump_383 assump_451
              apply False.elim assump_386
            let assump_382 := assump_1 assump_450
            apply False.elim assump_382
          case inr assump_377 =>
            cases assump_377
            case intro assump_396 assump_397 =>
              cases assump_397
              case intro assump_400 assump_401 =>
                have assump_452 : (((False → False) → False) → False) := by
                  intro assump_409
                  have assump_453 : (False → False) := by
                    intro assump_413
                    apply False.elim assump_413
                  let assump_412 := assump_409 assump_453
                  apply False.elim assump_412
                let assump_408 := assump_1 assump_452
                apply False.elim assump_408


variable (p2 p5 p4 : Prop)
theorem file1_18686 : ((((((True ∨ p5) → (p5 → False)) ∨ ((p5 → p2) → False)) → False) ∧ ((((p4 ∧ p2) ∧ (False ∧ p5)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p4 ∧ p2) ∧ (False ∧ p5)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p1 p3 p7 p6 : Prop)
theorem file1_19328 : (((((p7 ∧ False) → False) → False) → False) ∨ ((((p7 → False) ∧ (p1 → p7)) ∧ ((p3 ∨ True) → (p1 ∧ False))) ∧ (((p3 ∧ p6) → False) → ((p7 → p1) → False)))) := by
  apply Or.inl
  intro assump_5
  have assump_19 : ((p7 ∧ False) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p4 p1 : Prop)
theorem file1_19791 : ((((((True ∨ True) ∨ (p4 ∨ p1)) → False) → False) → False) → False) := by
  intro assump_5
  have assump_19 : ((((True ∨ True) ∨ (p4 ∨ p1)) → False) → False) := by
    intro assump_9
    have assump_20 : ((True ∨ True) ∨ (p4 ∨ p1)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p3 p0 p1 p7 p4 p6 : Prop)
theorem file1_20286 : (((((True → False) ∧ (p4 ∧ False)) ∧ ((p3 → False) → False)) → (((p0 ∨ p6) ∧ (True ∨ p6)) ∧ ((False ∨ p6) ∧ (p7 → False)))) ∨ ((((p7 → p1) ∧ (p1 ∨ p6)) ∨ ((True → p1) ∧ (p3 ∨ p1))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  cases assump_1
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
  apply And.intro
  cases assump_1
  case intro assump_26 assump_27 =>
    cases assump_26
    case intro assump_28 assump_29 =>
      cases assump_29
      case intro assump_32 assump_33 =>
        apply False.elim assump_33
  intro assump_38
  cases assump_1
  case intro assump_41 assump_42 =>
    cases assump_41
    case intro assump_43 assump_44 =>
      cases assump_44
      case intro assump_47 assump_48 =>
        apply False.elim assump_48


variable (p0 p1 p4 p3 p6 p5 p2 : Prop)
theorem file1_21473 : ((((((p0 ∨ p2) ∧ (p2 → p3)) ∧ ((p2 ∨ p6) ∧ (p1 ∧ p0))) ∨ (((p6 → p5) ∧ (p4 ∧ True)) → ((p4 ∧ p0) ∨ (p6 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p0 ∨ p2) ∧ (p2 → p3)) ∧ ((p2 ∨ p6) ∧ (p1 ∧ p0))) ∨ (((p6 → p5) ∧ (p4 ∧ True)) → ((p4 ∧ p0) ∨ (p6 ∨ True)))) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p6 p4 p0 p1 p5 : Prop)
theorem file1_22109 : ((((((p4 → p4) ∨ (p1 → p3)) → False) ∧ (((p0 → p6) → (True ∨ p6)) ∨ ((p1 → p4) ∨ (p4 → False)))) ∧ ((((p6 ∨ p5) → False) ∧ ((False → p4) ∧ (p4 → p1))) ∧ (((True ∧ False) → (p3 ∨ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              have assump_93 : ((True ∧ False) → (p3 ∨ p5)) := by
                intro assump_27
                cases assump_27
                case intro assump_28 assump_29 =>
                  apply False.elim assump_29
              let assump_26 := assump_13 assump_93
              apply False.elim assump_26
      case inr assump_9 =>
        cases assump_9
        case inl assump_37 =>
          cases assump_3
          case intro assump_41 assump_42 =>
            cases assump_41
            case intro assump_43 assump_44 =>
              cases assump_44
              case intro assump_47 assump_48 =>
                have assump_94 : ((True ∧ False) → (p3 ∨ p5)) := by
                  intro assump_56
                  cases assump_56
                  case intro assump_57 assump_58 =>
                    apply False.elim assump_58
                let assump_55 := assump_42 assump_94
                apply False.elim assump_55
        case inr assump_38 =>
          cases assump_3
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              cases assump_71
              case intro assump_74 assump_75 =>
                have assump_95 : ((True ∧ False) → (p3 ∨ p5)) := by
                  intro assump_83
                  cases assump_83
                  case intro assump_84 assump_85 =>
                    apply False.elim assump_85
                let assump_82 := assump_69 assump_95
                apply False.elim assump_82


variable (p1 p4 p6 p2 p0 p5 p7 : Prop)
theorem file1_24292 : (((((False ∧ p6) ∨ (p7 ∧ p6)) ∧ ((False ∧ p1) ∧ (True → False))) ∨ (((False → False) → False) → ((p5 ∧ p2) → False))) ∨ ((((p4 → p4) ∧ (p7 → p4)) ∨ ((True → p2) ∧ (p5 → False))) ∧ (((p7 → False) → (p0 ∧ p4)) → False))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_18 : (False → False) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_1 assump_18
    apply False.elim assump_11


variable (p7 p2 p5 p3 p0 p4 p1 p6 : Prop)
theorem file1_24867 : (((((p3 → p3) → False) → False) ∨ (((p3 → False) ∨ (True ∧ p4)) ∨ ((p6 ∧ False) → False))) → ((((p0 ∨ True) → False) → ((p0 ∨ p7) ∨ (p1 ∧ True))) ∨ (((p5 → p5) ∧ (p2 ∧ p4)) ∨ ((p2 ∨ p6) ∨ (p2 ∨ p4))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_48 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_9 := assump_6 assump_48
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        apply Or.inl
        intro assump_19
        have assump_49 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_22 := assump_19 assump_49
        apply False.elim assump_22
      case inr assump_16 =>
        cases assump_16
        case intro assump_26 assump_27 =>
          apply Or.inl
          intro assump_32
          have assump_50 : (p0 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_35 := assump_32 assump_50
          apply False.elim assump_35
    case inr assump_14 =>
      apply Or.inl
      intro assump_41
      have assump_51 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_44 := assump_41 assump_51
      apply False.elim assump_44


variable (p5 p4 p6 p0 p7 p2 : Prop)
theorem file1_26270 : ((((((p5 ∧ p6) ∨ (p4 → False)) → ((False ∧ False) ∧ (p0 → False))) ∨ (((p7 ∨ p2) ∨ (p4 → False)) ∧ ((p4 → False) ∨ (p0 ∨ p7)))) ∧ ((((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_150 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
        apply Or.inl
        intro assump_11
        intro assump_12
        apply False.elim assump_12
      let assump_10 := assump_3 assump_150
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            cases assump_19
            case inl assump_26 =>
              have assump_151 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                apply Or.inl
                intro assump_33
                intro assump_34
                apply False.elim assump_34
              let assump_32 := assump_3 assump_151
              apply False.elim assump_32
            case inr assump_27 =>
              cases assump_27
              case inl assump_40 =>
                have assump_152 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                  apply Or.inl
                  intro assump_47
                  intro assump_48
                  apply False.elim assump_48
                let assump_46 := assump_3 assump_152
                apply False.elim assump_46
              case inr assump_41 =>
                have assump_153 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                  apply Or.inl
                  intro assump_59
                  intro assump_60
                  apply False.elim assump_60
                let assump_58 := assump_3 assump_153
                apply False.elim assump_58
          case inr assump_23 =>
            cases assump_19
            case inl assump_68 =>
              have assump_154 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                apply Or.inl
                intro assump_75
                intro assump_76
                apply False.elim assump_76
              let assump_74 := assump_3 assump_154
              apply False.elim assump_74
            case inr assump_69 =>
              cases assump_69
              case inl assump_82 =>
                have assump_155 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                  apply Or.inl
                  intro assump_89
                  intro assump_90
                  apply False.elim assump_90
                let assump_88 := assump_3 assump_155
                apply False.elim assump_88
              case inr assump_83 =>
                have assump_156 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                  apply Or.inl
                  intro assump_101
                  intro assump_102
                  apply False.elim assump_102
                let assump_100 := assump_3 assump_156
                apply False.elim assump_100
        case inr assump_21 =>
          cases assump_19
          case inl assump_110 =>
            have assump_157 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
              apply Or.inl
              intro assump_117
              intro assump_118
              apply False.elim assump_118
            let assump_116 := assump_3 assump_157
            apply False.elim assump_116
          case inr assump_111 =>
            cases assump_111
            case inl assump_124 =>
              have assump_158 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                apply Or.inl
                intro assump_131
                intro assump_132
                apply False.elim assump_132
              let assump_130 := assump_3 assump_158
              apply False.elim assump_130
            case inr assump_125 =>
              have assump_159 : (((p2 ∨ p4) → (False → False)) ∨ ((p2 ∨ p5) → False)) := by
                apply Or.inl
                intro assump_143
                intro assump_144
                apply False.elim assump_144
              let assump_142 := assump_3 assump_159
              apply False.elim assump_142


variable (p0 p1 p2 p4 p6 p5 p7 p3 : Prop)
theorem file1_30711 : (((((p1 ∨ p5) ∧ (p2 ∧ p1)) → False) → False) → ((((p5 ∨ True) ∨ (p7 → False)) ∨ ((p3 → p7) → (p0 ∨ p5))) ∨ (((p1 ∨ p5) ∧ (True ∧ p5)) ∨ ((p4 → p3) ∨ (p2 → p6))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p0 p3 p2 p6 p1 p5 p4 : Prop)
theorem file1_31039 : ((((((p5 → p5) ∧ (p5 ∧ p4)) ∧ ((False → p2) ∨ (False → p1))) → False) ∧ ((((p0 → p6) ∨ (p2 ∨ p2)) ∨ ((p2 ∧ p2) ∨ (False → p1))) ∧ (((True ∨ p2) ∨ (p3 ∧ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_60 : ((True ∨ p2) ∨ (p3 ∧ p5)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_16 := assump_7 assump_60
          apply False.elim assump_16
        case inr assump_11 =>
          cases assump_11
          case inl assump_20 =>
            have assump_61 : ((True ∨ p2) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_26 := assump_7 assump_61
            apply False.elim assump_26
          case inr assump_21 =>
            have assump_62 : ((True ∨ p2) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_34 := assump_7 assump_62
            apply False.elim assump_34
      case inr assump_9 =>
        cases assump_9
        case inl assump_38 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            have assump_63 : ((True ∨ p2) ∨ (p3 ∧ p5)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_48 := assump_7 assump_63
            apply False.elim assump_48
        case inr assump_39 =>
          have assump_64 : ((True ∨ p2) ∨ (p3 ∧ p5)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_56 := assump_7 assump_64
          apply False.elim assump_56


variable (p6 p0 p3 p2 p4 : Prop)
theorem file1_32944 : ((((((p0 → False) ∧ (False ∨ p2)) → ((p2 ∧ True) ∨ (p3 ∧ p3))) ∨ (((False → p6) → False) ∧ ((p4 ∧ p6) ∧ (p4 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p0 → False) ∧ (False ∨ p2)) → ((p2 ∧ True) ∨ (p3 ∧ p3))) ∨ (((False → p6) → False) ∧ ((p4 ∧ p6) ∧ (p4 ∨ p6)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply False.elim assump_10
      case inr assump_11 =>
        apply Or.inl
        apply And.intro
        exact assump_11
        apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p0 p4 p6 p1 p5 : Prop)
theorem file1_33664 : (((((False → False) → False) ∧ ((False ∧ p0) ∨ (p6 → False))) → (((p5 → p2) → False) → False)) ∨ ((((p4 → False) → (p1 → p6)) → False) ∧ (((p0 → False) → (p2 ∨ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    case inr assump_10 =>
      have assump_25 : (False → False) := by
        intro assump_19
        apply False.elim assump_19
      let assump_18 := assump_5 assump_25
      apply False.elim assump_18


variable (p5 p0 p4 p3 p2 p7 p6 : Prop)
theorem file1_34354 : ((((((p6 ∧ p5) → (p0 → p4)) → False) → (((p0 → False) ∨ (p3 → p7)) → ((p5 ∧ p4) → (p2 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_99 : ((((p6 ∧ p5) → (p0 → p4)) → False) → (((p0 → False) ∨ (p3 → p7)) → ((p5 ∧ p4) → (p2 ∧ p0)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        have assump_100 : ((p6 ∧ p5) → (p0 → p4)) := by
          intro assump_21
          intro assump_22
          cases assump_21
          case intro assump_25 assump_26 =>
            exact assump_9
        let assump_20 := assump_5 assump_100
        apply False.elim assump_20
      case inr assump_15 =>
        have assump_101 : ((p6 ∧ p5) → (p0 → p4)) := by
          intro assump_39
          intro assump_40
          cases assump_39
          case intro assump_43 assump_44 =>
            exact assump_9
        let assump_38 := assump_5 assump_101
        apply False.elim assump_38
    cases assump_7
    case intro assump_52 assump_53 =>
      cases assump_6
      case inl assump_58 =>
        have assump_102 : ((p6 ∧ p5) → (p0 → p4)) := by
          intro assump_65
          intro assump_66
          cases assump_65
          case intro assump_69 assump_70 =>
            exact assump_53
        let assump_64 := assump_5 assump_102
        apply False.elim assump_64
      case inr assump_59 =>
        have assump_103 : ((p6 ∧ p5) → (p0 → p4)) := by
          intro assump_83
          intro assump_84
          cases assump_83
          case intro assump_87 assump_88 =>
            exact assump_53
        let assump_82 := assump_5 assump_103
        apply False.elim assump_82
  let assump_4 := assump_1 assump_99
  apply False.elim assump_4


variable (p5 p0 p2 p4 p1 p7 p6 p3 : Prop)
theorem file1_36224 : (((((p5 → True) ∨ (p0 → False)) → False) ∧ (((p6 → False) ∨ (p6 ∨ p6)) ∧ ((p3 ∨ p7) → (p4 → False)))) → ((((p2 → p5) → (p6 ∨ p5)) ∨ ((p1 ∧ p7) ∨ (p4 ∨ p5))) ∧ (((p6 → p1) → (p3 → False)) ∧ ((p2 → False) ∨ (p5 → False))))) := by
  intro assump_17
  apply And.intro
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      cases assump_22
      case inl assump_24 =>
        apply Or.inl
        intro assump_30
        have assump_164 : ((p5 → True) ∨ (p0 → False)) := by
          apply Or.inl
          intro assump_37
          apply True.intro
        let assump_36 := assump_18 assump_164
        apply False.elim assump_36
      case inr assump_25 =>
        cases assump_25
        case inl assump_41 =>
          apply Or.inl
          intro assump_47
          apply Or.inl
          exact assump_41
        case inr assump_42 =>
          apply Or.inl
          intro assump_54
          apply Or.inl
          exact assump_42
  apply And.intro
  intro assump_57
  intro assump_58
  cases assump_17
  case intro assump_63 assump_64 =>
    cases assump_64
    case intro assump_67 assump_68 =>
      cases assump_67
      case inl assump_69 =>
        have assump_165 : ((p5 → True) ∨ (p0 → False)) := by
          apply Or.inl
          intro assump_79
          apply True.intro
        let assump_78 := assump_63 assump_165
        apply False.elim assump_78
      case inr assump_70 =>
        cases assump_70
        case inl assump_83 =>
          have assump_166 : ((p5 → True) ∨ (p0 → False)) := by
            apply Or.inl
            intro assump_93
            apply True.intro
          let assump_92 := assump_63 assump_166
          apply False.elim assump_92
        case inr assump_84 =>
          have assump_167 : ((p5 → True) ∨ (p0 → False)) := by
            apply Or.inl
            intro assump_105
            apply True.intro
          let assump_104 := assump_63 assump_167
          apply False.elim assump_104
  cases assump_17
  case intro assump_109 assump_110 =>
    cases assump_110
    case intro assump_113 assump_114 =>
      cases assump_113
      case inl assump_115 =>
        apply Or.inl
        intro assump_121
        have assump_168 : ((p5 → True) ∨ (p0 → False)) := by
          apply Or.inl
          intro assump_128
          apply True.intro
        let assump_127 := assump_109 assump_168
        apply False.elim assump_127
      case inr assump_116 =>
        cases assump_116
        case inl assump_132 =>
          apply Or.inl
          intro assump_138
          have assump_169 : ((p5 → True) ∨ (p0 → False)) := by
            apply Or.inl
            intro assump_145
            apply True.intro
          let assump_144 := assump_109 assump_169
          apply False.elim assump_144
        case inr assump_133 =>
          apply Or.inl
          intro assump_153
          have assump_170 : ((p5 → True) ∨ (p0 → False)) := by
            apply Or.inl
            intro assump_160
            apply True.intro
          let assump_159 := assump_109 assump_170
          apply False.elim assump_159


variable (p3 p0 p2 : Prop)
theorem file1_39402 : ((((((False → False) → False) ∧ ((p0 ∧ p0) → (p3 → p2))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → False) → False) ∧ ((p0 ∧ p0) → (p3 → p2))) → False) := by
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


variable (p7 p2 p5 p4 p3 p0 p6 : Prop)
theorem file1_39979 : (((((p5 → False) → (p7 ∨ True)) → False) → (((False ∧ True) → False) ∨ ((p2 → False) ∧ (p3 ∨ p0)))) → ((((False → p6) ∨ (p4 ∧ True)) ∧ ((True ∨ p4) → (True ∨ p4))) ∨ (((p6 ∧ False) → (p4 → p3)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    apply Or.inl
    apply True.intro
  case inr assump_9 =>
    apply Or.inl
    apply True.intro


variable (p2 p4 p3 p0 p5 : Prop)
theorem file1_40513 : (((((True ∧ True) → False) → False) ∧ (((p5 → p5) → False) → ((p5 → False) → (True ∧ p0)))) ∨ ((((False ∨ p3) → (p2 → False)) ∧ ((p4 ∧ p3) → (p0 ∧ p2))) ∧ (((p3 → True) → (False ∨ False)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_21 : (True ∧ True) := by
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4
  intro assump_8
  intro assump_9
  apply And.intro
  apply True.intro
  have assump_22 : (p5 → p5) := by
    intro assump_15
    exact assump_15
  let assump_14 := assump_8 assump_22
  apply False.elim assump_14


variable (p1 p6 : Prop)
theorem file1_41195 : ((((((False → p1) → (p6 → p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → p1) → (p6 → p6)) → False) → False) := by
    intro assump_5
    have assump_22 : ((False → p1) → (p6 → p6)) := by
      intro assump_9
      intro assump_10
      exact assump_10
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p5 p7 p4 p3 p0 : Prop)
theorem file1_41689 : (((((True ∨ p4) → (p7 → False)) ∨ ((False → p5) → False)) ∧ (((p5 → p3) ∧ (True ∨ p3)) ∧ ((True ∨ p3) ∧ (p3 → p0)))) → ((((p7 ∨ p1) ∧ (p5 ∧ p1)) ∧ ((p4 ∧ False) → (p0 ∨ p1))) → (((p7 ∨ True) ∧ (p3 ∨ p0)) → ((p1 → False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_8
      case inl assump_13 =>
        cases assump_2
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_20
              case intro assump_25 assump_26 =>
                cases assump_1
                case intro assump_33 assump_34 =>
                  cases assump_33
                  case inl assump_35 =>
                    cases assump_34
                    case intro assump_39 assump_40 =>
                      cases assump_39
                      case intro assump_41 assump_42 =>
                        cases assump_42
                        case inl assump_45 =>
                          cases assump_40
                          case intro assump_49 assump_50 =>
                            cases assump_49
                            case inl assump_51 =>
                              have assump_1515 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_61 := assump_35 assump_1515
                              have assump_1516 : p7 := by
                                exact assump_21
                              let assump_62 := assump_61 assump_1516
                              apply False.elim assump_62
                            case inr assump_52 =>
                              have assump_1517 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_75 := assump_35 assump_1517
                              have assump_1518 : p7 := by
                                exact assump_21
                              let assump_76 := assump_75 assump_1518
                              apply False.elim assump_76
                        case inr assump_46 =>
                          cases assump_40
                          case intro assump_82 assump_83 =>
                            cases assump_82
                            case inl assump_84 =>
                              have assump_1519 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_95 := assump_35 assump_1519
                              have assump_1520 : p7 := by
                                exact assump_21
                              let assump_96 := assump_95 assump_1520
                              apply False.elim assump_96
                            case inr assump_85 =>
                              have assump_1521 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_110 := assump_35 assump_1521
                              have assump_1522 : p7 := by
                                exact assump_21
                              let assump_111 := assump_110 assump_1522
                              apply False.elim assump_111
                  case inr assump_36 =>
                    cases assump_34
                    case intro assump_117 assump_118 =>
                      cases assump_117
                      case intro assump_119 assump_120 =>
                        cases assump_120
                        case inl assump_123 =>
                          cases assump_118
                          case intro assump_127 assump_128 =>
                            cases assump_127
                            case inl assump_129 =>
                              have assump_1523 : (False → p5) := by
                                intro assump_140
                                apply False.elim assump_140
                              let assump_139 := assump_36 assump_1523
                              apply False.elim assump_139
                            case inr assump_130 =>
                              have assump_1524 : (False → p5) := by
                                intro assump_156
                                apply False.elim assump_156
                              let assump_155 := assump_36 assump_1524
                              apply False.elim assump_155
                        case inr assump_124 =>
                          cases assump_118
                          case intro assump_164 assump_165 =>
                            cases assump_164
                            case inl assump_166 =>
                              have assump_1525 : (False → p5) := by
                                intro assump_178
                                apply False.elim assump_178
                              let assump_177 := assump_36 assump_1525
                              apply False.elim assump_177
                            case inr assump_167 =>
                              have assump_1526 : (False → p5) := by
                                intro assump_195
                                apply False.elim assump_195
                              let assump_194 := assump_36 assump_1526
                              apply False.elim assump_194
            case inr assump_22 =>
              cases assump_20
              case intro assump_203 assump_204 =>
                cases assump_1
                case intro assump_211 assump_212 =>
                  cases assump_211
                  case inl assump_213 =>
                    cases assump_212
                    case intro assump_217 assump_218 =>
                      cases assump_217
                      case intro assump_219 assump_220 =>
                        cases assump_220
                        case inl assump_223 =>
                          cases assump_218
                          case intro assump_227 assump_228 =>
                            cases assump_227
                            case inl assump_229 =>
                              have assump_1527 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_239 := assump_213 assump_1527
                              have assump_1528 : p7 := by
                                exact assump_9
                              let assump_240 := assump_239 assump_1528
                              apply False.elim assump_240
                            case inr assump_230 =>
                              have assump_1529 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_253 := assump_213 assump_1529
                              have assump_1530 : p7 := by
                                exact assump_9
                              let assump_254 := assump_253 assump_1530
                              apply False.elim assump_254
                        case inr assump_224 =>
                          cases assump_218
                          case intro assump_260 assump_261 =>
                            cases assump_260
                            case inl assump_262 =>
                              have assump_1531 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_273 := assump_213 assump_1531
                              have assump_1532 : p7 := by
                                exact assump_9
                              let assump_274 := assump_273 assump_1532
                              apply False.elim assump_274
                            case inr assump_263 =>
                              have assump_1533 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_288 := assump_213 assump_1533
                              have assump_1534 : p7 := by
                                exact assump_9
                              let assump_289 := assump_288 assump_1534
                              apply False.elim assump_289
                  case inr assump_214 =>
                    cases assump_212
                    case intro assump_295 assump_296 =>
                      cases assump_295
                      case intro assump_297 assump_298 =>
                        cases assump_298
                        case inl assump_301 =>
                          cases assump_296
                          case intro assump_305 assump_306 =>
                            cases assump_305
                            case inl assump_307 =>
                              have assump_1535 : (False → p5) := by
                                intro assump_318
                                apply False.elim assump_318
                              let assump_317 := assump_214 assump_1535
                              apply False.elim assump_317
                            case inr assump_308 =>
                              have assump_1536 : (False → p5) := by
                                intro assump_334
                                apply False.elim assump_334
                              let assump_333 := assump_214 assump_1536
                              apply False.elim assump_333
                        case inr assump_302 =>
                          cases assump_296
                          case intro assump_342 assump_343 =>
                            cases assump_342
                            case inl assump_344 =>
                              have assump_1537 : (False → p5) := by
                                intro assump_356
                                apply False.elim assump_356
                              let assump_355 := assump_214 assump_1537
                              apply False.elim assump_355
                            case inr assump_345 =>
                              have assump_1538 : (False → p5) := by
                                intro assump_373
                                apply False.elim assump_373
                              let assump_372 := assump_214 assump_1538
                              apply False.elim assump_372
      case inr assump_14 =>
        cases assump_2
        case intro assump_381 assump_382 =>
          cases assump_381
          case intro assump_383 assump_384 =>
            cases assump_383
            case inl assump_385 =>
              cases assump_384
              case intro assump_389 assump_390 =>
                cases assump_1
                case intro assump_397 assump_398 =>
                  cases assump_397
                  case inl assump_399 =>
                    cases assump_398
                    case intro assump_403 assump_404 =>
                      cases assump_403
                      case intro assump_405 assump_406 =>
                        cases assump_406
                        case inl assump_409 =>
                          cases assump_404
                          case intro assump_413 assump_414 =>
                            cases assump_413
                            case inl assump_415 =>
                              have assump_1539 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_424 := assump_399 assump_1539
                              have assump_1540 : p7 := by
                                exact assump_385
                              let assump_425 := assump_424 assump_1540
                              apply False.elim assump_425
                            case inr assump_416 =>
                              have assump_1541 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_438 := assump_399 assump_1541
                              have assump_1542 : p7 := by
                                exact assump_385
                              let assump_439 := assump_438 assump_1542
                              apply False.elim assump_439
                        case inr assump_410 =>
                          cases assump_404
                          case intro assump_445 assump_446 =>
                            cases assump_445
                            case inl assump_447 =>
                              have assump_1543 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_458 := assump_399 assump_1543
                              have assump_1544 : p7 := by
                                exact assump_385
                              let assump_459 := assump_458 assump_1544
                              apply False.elim assump_459
                            case inr assump_448 =>
                              have assump_1545 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_473 := assump_399 assump_1545
                              have assump_1546 : p7 := by
                                exact assump_385
                              let assump_474 := assump_473 assump_1546
                              apply False.elim assump_474
                  case inr assump_400 =>
                    cases assump_398
                    case intro assump_480 assump_481 =>
                      cases assump_480
                      case intro assump_482 assump_483 =>
                        cases assump_483
                        case inl assump_486 =>
                          cases assump_481
                          case intro assump_490 assump_491 =>
                            cases assump_490
                            case inl assump_492 =>
                              have assump_1547 : (False → p5) := by
                                intro assump_502
                                apply False.elim assump_502
                              let assump_501 := assump_400 assump_1547
                              apply False.elim assump_501
                            case inr assump_493 =>
                              have assump_1548 : (False → p5) := by
                                intro assump_518
                                apply False.elim assump_518
                              let assump_517 := assump_400 assump_1548
                              apply False.elim assump_517
                        case inr assump_487 =>
                          cases assump_481
                          case intro assump_526 assump_527 =>
                            cases assump_526
                            case inl assump_528 =>
                              have assump_1549 : (False → p5) := by
                                intro assump_540
                                apply False.elim assump_540
                              let assump_539 := assump_400 assump_1549
                              apply False.elim assump_539
                            case inr assump_529 =>
                              have assump_1550 : (False → p5) := by
                                intro assump_557
                                apply False.elim assump_557
                              let assump_556 := assump_400 assump_1550
                              apply False.elim assump_556
            case inr assump_386 =>
              cases assump_384
              case intro assump_565 assump_566 =>
                cases assump_1
                case intro assump_573 assump_574 =>
                  cases assump_573
                  case inl assump_575 =>
                    cases assump_574
                    case intro assump_579 assump_580 =>
                      cases assump_579
                      case intro assump_581 assump_582 =>
                        cases assump_582
                        case inl assump_585 =>
                          cases assump_580
                          case intro assump_589 assump_590 =>
                            cases assump_589
                            case inl assump_591 =>
                              have assump_1551 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_600 := assump_575 assump_1551
                              have assump_1552 : p7 := by
                                exact assump_9
                              let assump_601 := assump_600 assump_1552
                              apply False.elim assump_601
                            case inr assump_592 =>
                              have assump_1553 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_614 := assump_575 assump_1553
                              have assump_1554 : p7 := by
                                exact assump_9
                              let assump_615 := assump_614 assump_1554
                              apply False.elim assump_615
                        case inr assump_586 =>
                          cases assump_580
                          case intro assump_621 assump_622 =>
                            cases assump_621
                            case inl assump_623 =>
                              have assump_1555 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_634 := assump_575 assump_1555
                              have assump_1556 : p7 := by
                                exact assump_9
                              let assump_635 := assump_634 assump_1556
                              apply False.elim assump_635
                            case inr assump_624 =>
                              have assump_1557 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_649 := assump_575 assump_1557
                              have assump_1558 : p7 := by
                                exact assump_9
                              let assump_650 := assump_649 assump_1558
                              apply False.elim assump_650
                  case inr assump_576 =>
                    cases assump_574
                    case intro assump_656 assump_657 =>
                      cases assump_656
                      case intro assump_658 assump_659 =>
                        cases assump_659
                        case inl assump_662 =>
                          cases assump_657
                          case intro assump_666 assump_667 =>
                            cases assump_666
                            case inl assump_668 =>
                              have assump_1559 : (False → p5) := by
                                intro assump_678
                                apply False.elim assump_678
                              let assump_677 := assump_576 assump_1559
                              apply False.elim assump_677
                            case inr assump_669 =>
                              have assump_1560 : (False → p5) := by
                                intro assump_694
                                apply False.elim assump_694
                              let assump_693 := assump_576 assump_1560
                              apply False.elim assump_693
                        case inr assump_663 =>
                          cases assump_657
                          case intro assump_702 assump_703 =>
                            cases assump_702
                            case inl assump_704 =>
                              have assump_1561 : (False → p5) := by
                                intro assump_716
                                apply False.elim assump_716
                              let assump_715 := assump_576 assump_1561
                              apply False.elim assump_715
                            case inr assump_705 =>
                              have assump_1562 : (False → p5) := by
                                intro assump_733
                                apply False.elim assump_733
                              let assump_732 := assump_576 assump_1562
                              apply False.elim assump_732
    case inr assump_10 =>
      cases assump_8
      case inl assump_741 =>
        cases assump_2
        case intro assump_745 assump_746 =>
          cases assump_745
          case intro assump_747 assump_748 =>
            cases assump_747
            case inl assump_749 =>
              cases assump_748
              case intro assump_753 assump_754 =>
                cases assump_1
                case intro assump_761 assump_762 =>
                  cases assump_761
                  case inl assump_763 =>
                    cases assump_762
                    case intro assump_767 assump_768 =>
                      cases assump_767
                      case intro assump_769 assump_770 =>
                        cases assump_770
                        case inl assump_773 =>
                          cases assump_768
                          case intro assump_777 assump_778 =>
                            cases assump_777
                            case inl assump_779 =>
                              have assump_1563 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_789 := assump_763 assump_1563
                              have assump_1564 : p7 := by
                                exact assump_749
                              let assump_790 := assump_789 assump_1564
                              apply False.elim assump_790
                            case inr assump_780 =>
                              have assump_1565 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_803 := assump_763 assump_1565
                              have assump_1566 : p7 := by
                                exact assump_749
                              let assump_804 := assump_803 assump_1566
                              apply False.elim assump_804
                        case inr assump_774 =>
                          cases assump_768
                          case intro assump_810 assump_811 =>
                            cases assump_810
                            case inl assump_812 =>
                              have assump_1567 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_823 := assump_763 assump_1567
                              have assump_1568 : p7 := by
                                exact assump_749
                              let assump_824 := assump_823 assump_1568
                              apply False.elim assump_824
                            case inr assump_813 =>
                              have assump_1569 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_838 := assump_763 assump_1569
                              have assump_1570 : p7 := by
                                exact assump_749
                              let assump_839 := assump_838 assump_1570
                              apply False.elim assump_839
                  case inr assump_764 =>
                    cases assump_762
                    case intro assump_845 assump_846 =>
                      cases assump_845
                      case intro assump_847 assump_848 =>
                        cases assump_848
                        case inl assump_851 =>
                          cases assump_846
                          case intro assump_855 assump_856 =>
                            cases assump_855
                            case inl assump_857 =>
                              have assump_1571 : (False → p5) := by
                                intro assump_868
                                apply False.elim assump_868
                              let assump_867 := assump_764 assump_1571
                              apply False.elim assump_867
                            case inr assump_858 =>
                              have assump_1572 : (False → p5) := by
                                intro assump_884
                                apply False.elim assump_884
                              let assump_883 := assump_764 assump_1572
                              apply False.elim assump_883
                        case inr assump_852 =>
                          cases assump_846
                          case intro assump_892 assump_893 =>
                            cases assump_892
                            case inl assump_894 =>
                              have assump_1573 : (False → p5) := by
                                intro assump_906
                                apply False.elim assump_906
                              let assump_905 := assump_764 assump_1573
                              apply False.elim assump_905
                            case inr assump_895 =>
                              have assump_1574 : (False → p5) := by
                                intro assump_923
                                apply False.elim assump_923
                              let assump_922 := assump_764 assump_1574
                              apply False.elim assump_922
            case inr assump_750 =>
              cases assump_748
              case intro assump_931 assump_932 =>
                cases assump_1
                case intro assump_939 assump_940 =>
                  cases assump_939
                  case inl assump_941 =>
                    cases assump_940
                    case intro assump_945 assump_946 =>
                      cases assump_945
                      case intro assump_947 assump_948 =>
                        cases assump_948
                        case inl assump_951 =>
                          cases assump_946
                          case intro assump_955 assump_956 =>
                            cases assump_955
                            case inl assump_957 =>
                              have assump_1575 : p1 := by
                                exact assump_932
                              let assump_974 := assump_4 assump_1575
                              apply False.elim assump_974
                            case inr assump_958 =>
                              have assump_1576 : p1 := by
                                exact assump_932
                              let assump_994 := assump_4 assump_1576
                              apply False.elim assump_994
                        case inr assump_952 =>
                          cases assump_946
                          case intro assump_1000 assump_1001 =>
                            cases assump_1000
                            case inl assump_1002 =>
                              have assump_1577 : p1 := by
                                exact assump_932
                              let assump_1020 := assump_4 assump_1577
                              apply False.elim assump_1020
                            case inr assump_1003 =>
                              have assump_1578 : p1 := by
                                exact assump_932
                              let assump_1041 := assump_4 assump_1578
                              apply False.elim assump_1041
                  case inr assump_942 =>
                    cases assump_940
                    case intro assump_1047 assump_1048 =>
                      cases assump_1047
                      case intro assump_1049 assump_1050 =>
                        cases assump_1050
                        case inl assump_1053 =>
                          cases assump_1048
                          case intro assump_1057 assump_1058 =>
                            cases assump_1057
                            case inl assump_1059 =>
                              have assump_1579 : (False → p5) := by
                                intro assump_1070
                                apply False.elim assump_1070
                              let assump_1069 := assump_942 assump_1579
                              apply False.elim assump_1069
                            case inr assump_1060 =>
                              have assump_1580 : (False → p5) := by
                                intro assump_1086
                                apply False.elim assump_1086
                              let assump_1085 := assump_942 assump_1580
                              apply False.elim assump_1085
                        case inr assump_1054 =>
                          cases assump_1048
                          case intro assump_1094 assump_1095 =>
                            cases assump_1094
                            case inl assump_1096 =>
                              have assump_1581 : (False → p5) := by
                                intro assump_1108
                                apply False.elim assump_1108
                              let assump_1107 := assump_942 assump_1581
                              apply False.elim assump_1107
                            case inr assump_1097 =>
                              have assump_1582 : (False → p5) := by
                                intro assump_1125
                                apply False.elim assump_1125
                              let assump_1124 := assump_942 assump_1582
                              apply False.elim assump_1124
      case inr assump_742 =>
        cases assump_2
        case intro assump_1133 assump_1134 =>
          cases assump_1133
          case intro assump_1135 assump_1136 =>
            cases assump_1135
            case inl assump_1137 =>
              cases assump_1136
              case intro assump_1141 assump_1142 =>
                cases assump_1
                case intro assump_1149 assump_1150 =>
                  cases assump_1149
                  case inl assump_1151 =>
                    cases assump_1150
                    case intro assump_1155 assump_1156 =>
                      cases assump_1155
                      case intro assump_1157 assump_1158 =>
                        cases assump_1158
                        case inl assump_1161 =>
                          cases assump_1156
                          case intro assump_1165 assump_1166 =>
                            cases assump_1165
                            case inl assump_1167 =>
                              have assump_1583 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_1176 := assump_1151 assump_1583
                              have assump_1584 : p7 := by
                                exact assump_1137
                              let assump_1177 := assump_1176 assump_1584
                              apply False.elim assump_1177
                            case inr assump_1168 =>
                              have assump_1585 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_1190 := assump_1151 assump_1585
                              have assump_1586 : p7 := by
                                exact assump_1137
                              let assump_1191 := assump_1190 assump_1586
                              apply False.elim assump_1191
                        case inr assump_1162 =>
                          cases assump_1156
                          case intro assump_1197 assump_1198 =>
                            cases assump_1197
                            case inl assump_1199 =>
                              have assump_1587 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_1210 := assump_1151 assump_1587
                              have assump_1588 : p7 := by
                                exact assump_1137
                              let assump_1211 := assump_1210 assump_1588
                              apply False.elim assump_1211
                            case inr assump_1200 =>
                              have assump_1589 : (True ∨ p4) := by
                                apply Or.inl
                                apply True.intro
                              let assump_1225 := assump_1151 assump_1589
                              have assump_1590 : p7 := by
                                exact assump_1137
                              let assump_1226 := assump_1225 assump_1590
                              apply False.elim assump_1226
                  case inr assump_1152 =>
                    cases assump_1150
                    case intro assump_1232 assump_1233 =>
                      cases assump_1232
                      case intro assump_1234 assump_1235 =>
                        cases assump_1235
                        case inl assump_1238 =>
                          cases assump_1233
                          case intro assump_1242 assump_1243 =>
                            cases assump_1242
                            case inl assump_1244 =>
                              have assump_1591 : (False → p5) := by
                                intro assump_1254
                                apply False.elim assump_1254
                              let assump_1253 := assump_1152 assump_1591
                              apply False.elim assump_1253
                            case inr assump_1245 =>
                              have assump_1592 : (False → p5) := by
                                intro assump_1270
                                apply False.elim assump_1270
                              let assump_1269 := assump_1152 assump_1592
                              apply False.elim assump_1269
                        case inr assump_1239 =>
                          cases assump_1233
                          case intro assump_1278 assump_1279 =>
                            cases assump_1278
                            case inl assump_1280 =>
                              have assump_1593 : (False → p5) := by
                                intro assump_1292
                                apply False.elim assump_1292
                              let assump_1291 := assump_1152 assump_1593
                              apply False.elim assump_1291
                            case inr assump_1281 =>
                              have assump_1594 : (False → p5) := by
                                intro assump_1309
                                apply False.elim assump_1309
                              let assump_1308 := assump_1152 assump_1594
                              apply False.elim assump_1308
            case inr assump_1138 =>
              cases assump_1136
              case intro assump_1317 assump_1318 =>
                cases assump_1
                case intro assump_1325 assump_1326 =>
                  cases assump_1325
                  case inl assump_1327 =>
                    cases assump_1326
                    case intro assump_1331 assump_1332 =>
                      cases assump_1331
                      case intro assump_1333 assump_1334 =>
                        cases assump_1334
                        case inl assump_1337 =>
                          cases assump_1332
                          case intro assump_1341 assump_1342 =>
                            cases assump_1341
                            case inl assump_1343 =>
                              have assump_1595 : p1 := by
                                exact assump_1318
                              let assump_1359 := assump_4 assump_1595
                              apply False.elim assump_1359
                            case inr assump_1344 =>
                              have assump_1596 : p1 := by
                                exact assump_1318
                              let assump_1379 := assump_4 assump_1596
                              apply False.elim assump_1379
                        case inr assump_1338 =>
                          cases assump_1332
                          case intro assump_1385 assump_1386 =>
                            cases assump_1385
                            case inl assump_1387 =>
                              have assump_1597 : p1 := by
                                exact assump_1318
                              let assump_1405 := assump_4 assump_1597
                              apply False.elim assump_1405
                            case inr assump_1388 =>
                              have assump_1598 : p1 := by
                                exact assump_1318
                              let assump_1426 := assump_4 assump_1598
                              apply False.elim assump_1426
                  case inr assump_1328 =>
                    cases assump_1326
                    case intro assump_1432 assump_1433 =>
                      cases assump_1432
                      case intro assump_1434 assump_1435 =>
                        cases assump_1435
                        case inl assump_1438 =>
                          cases assump_1433
                          case intro assump_1442 assump_1443 =>
                            cases assump_1442
                            case inl assump_1444 =>
                              have assump_1599 : (False → p5) := by
                                intro assump_1454
                                apply False.elim assump_1454
                              let assump_1453 := assump_1328 assump_1599
                              apply False.elim assump_1453
                            case inr assump_1445 =>
                              have assump_1600 : (False → p5) := by
                                intro assump_1470
                                apply False.elim assump_1470
                              let assump_1469 := assump_1328 assump_1600
                              apply False.elim assump_1469
                        case inr assump_1439 =>
                          cases assump_1433
                          case intro assump_1478 assump_1479 =>
                            cases assump_1478
                            case inl assump_1480 =>
                              have assump_1601 : (False → p5) := by
                                intro assump_1492
                                apply False.elim assump_1492
                              let assump_1491 := assump_1328 assump_1601
                              apply False.elim assump_1491
                            case inr assump_1481 =>
                              have assump_1602 : (False → p5) := by
                                intro assump_1509
                                apply False.elim assump_1509
                              let assump_1508 := assump_1328 assump_1602
                              apply False.elim assump_1508


variable (p1 p7 : Prop)
theorem file1_81834 : ((((((True ∧ p7) → (p1 → p1)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True ∧ p7) → (p1 → p1)) → False) → False) := by
    intro assump_5
    have assump_26 : ((True ∧ p7) → (p1 → p1)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        exact assump_10
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p3 p5 p1 p2 p6 : Prop)
theorem file1_82388 : (((((p2 ∧ p3) → (p1 → p3)) → ((False → False) → False)) → (((p0 → False) ∨ (p2 → False)) → False)) ∨ ((((p6 → p2) → False) → ((p6 → p2) → (p5 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_49 : ((p2 ∧ p3) → (p1 → p3)) := by
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        exact assump_15
    let assump_9 := assump_1 assump_49
    have assump_50 : (False → False) := by
      intro assump_21
      apply False.elim assump_21
    let assump_20 := assump_9 assump_50
    apply False.elim assump_20
  case inr assump_4 =>
    have assump_51 : ((p2 ∧ p3) → (p1 → p3)) := by
      intro assump_32
      intro assump_33
      cases assump_32
      case intro assump_36 assump_37 =>
        exact assump_37
    let assump_31 := assump_1 assump_51
    have assump_52 : (False → False) := by
      intro assump_43
      apply False.elim assump_43
    let assump_42 := assump_31 assump_52
    apply False.elim assump_42


variable (p0 p6 p5 p2 p7 p3 p4 : Prop)
theorem file1_83512 : ((((((p2 ∨ p2) → False) → ((p6 → p2) ∧ (p7 ∨ p3))) ∨ (((p4 → False) ∨ (p6 → p2)) ∧ ((p0 ∨ p7) → False))) ∧ ((((p4 → p5) → (p2 ∨ True)) ∨ ((p0 ∧ p4) ∧ (False → False))) → False)) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case inl assump_13 =>
      have assump_56 : (((p4 → p5) → (p2 ∨ True)) ∨ ((p0 ∧ p4) ∧ (False → False))) := by
        apply Or.inl
        intro assump_20
        apply Or.inr
        apply True.intro
      let assump_19 := assump_12 assump_56
      apply False.elim assump_19
    case inr assump_14 =>
      cases assump_14
      case intro assump_26 assump_27 =>
        cases assump_26
        case inl assump_28 =>
          have assump_57 : (((p4 → p5) → (p2 ∨ True)) ∨ ((p0 ∧ p4) ∧ (False → False))) := by
            apply Or.inl
            intro assump_37
            apply Or.inr
            apply True.intro
          let assump_36 := assump_12 assump_57
          apply False.elim assump_36
        case inr assump_29 =>
          have assump_58 : (((p4 → p5) → (p2 ∨ True)) ∨ ((p0 ∧ p4) ∧ (False → False))) := by
            apply Or.inl
            intro assump_50
            apply Or.inr
            apply True.intro
          let assump_49 := assump_12 assump_58
          apply False.elim assump_49


variable (p2 p6 p0 p3 p7 p5 p1 p4 : Prop)
theorem file1_84885 : (((((p0 → p5) ∨ (p7 → p6)) ∧ ((True → False) → False)) → (((p2 → False) → (p3 ∧ p2)) → ((p1 ∧ True) → (p7 ∨ p3)))) → ((((p4 → p4) → False) → False) ∨ (((p0 ∨ p4) ∨ (p6 → False)) ∧ ((p3 ∨ p1) ∨ (p2 ∨ p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (p4 → p4) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p7 p0 p4 p6 : Prop)
theorem file1_85339 : (((((p7 → True) → False) ∧ ((True ∧ p0) → (True ∨ p4))) ∨ (((False ∧ False) → False) ∧ ((True ∨ p6) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_26 : (p7 → True) := by
        intro assump_12
        apply True.intro
      let assump_11 := assump_4 assump_26
      apply False.elim assump_11
  case inr assump_3 =>
    cases assump_3
    case intro assump_16 assump_17 =>
      have assump_27 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_22 := assump_17 assump_27
      apply False.elim assump_22


variable (p6 p0 p5 p2 p4 p1 p3 p7 : Prop)
theorem file1_86051 : (((((False ∨ False) → (True ∨ p4)) ∨ ((p2 ∨ p1) → (False ∨ False))) ∨ (((p1 ∨ p7) → False) ∨ ((p7 → p3) → (False ∧ p0)))) ∨ ((((p3 → True) ∨ (p0 ∧ p4)) ∧ ((p6 ∧ True) → (p0 ∧ p5))) ∧ (((True ∨ p6) → False) ∧ ((p6 ∧ p4) ∧ (p1 ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply False.elim assump_2
  case inr assump_3 =>
    apply False.elim assump_3


variable (p4 p3 p5 p0 p2 p7 p6 p1 : Prop)
theorem file1_86543 : (((((p0 ∧ p0) → (p4 ∧ p0)) → False) ∧ (((p1 ∨ p5) ∨ (p5 → False)) ∨ ((p0 → p3) → False))) → ((((p4 ∨ p2) → (p4 → False)) → ((p7 → p2) → (p4 → False))) ∨ (((p5 ∧ False) → (p0 → False)) → ((p6 → False) → (p5 ∨ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          intro assump_14
          intro assump_15
          intro assump_16
          have assump_76 : (p4 ∨ p2) := by
            apply Or.inl
            exact assump_16
          let assump_23 := assump_14 assump_76
          have assump_77 : p4 := by
            exact assump_16
          let assump_24 := assump_23 assump_77
          apply False.elim assump_24
        case inr assump_11 =>
          apply Or.inl
          intro assump_30
          intro assump_31
          intro assump_32
          have assump_78 : (p4 ∨ p2) := by
            apply Or.inl
            exact assump_32
          let assump_39 := assump_30 assump_78
          have assump_79 : p4 := by
            exact assump_32
          let assump_40 := assump_39 assump_79
          apply False.elim assump_40
      case inr assump_9 =>
        apply Or.inl
        intro assump_46
        intro assump_47
        intro assump_48
        have assump_80 : (p4 ∨ p2) := by
          apply Or.inl
          exact assump_48
        let assump_55 := assump_46 assump_80
        have assump_81 : p4 := by
          exact assump_48
        let assump_56 := assump_55 assump_81
        apply False.elim assump_56
    case inr assump_7 =>
      apply Or.inl
      intro assump_62
      intro assump_63
      intro assump_64
      have assump_82 : (p4 ∨ p2) := by
        apply Or.inl
        exact assump_64
      let assump_71 := assump_62 assump_82
      have assump_83 : p4 := by
        exact assump_64
      let assump_72 := assump_71 assump_83
      apply False.elim assump_72


variable (p4 p2 p5 p3 p6 p0 : Prop)
theorem file1_88616 : (((((False → False) → (p6 → p6)) → ((True → False) ∧ (p5 → p3))) ∧ (((False ∨ p4) → False) ∧ ((p2 ∧ p4) ∧ (p0 ∨ p3)))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_25
          case inl assump_32 =>
            have assump_52 : (False ∨ p4) := by
              apply Or.inr
              exact assump_27
            let assump_39 := assump_20 assump_52
            apply False.elim assump_39
          case inr assump_33 =>
            have assump_53 : (False ∨ p4) := by
              apply Or.inr
              exact assump_27
            let assump_48 := assump_20 assump_53
            apply False.elim assump_48


variable (p7 p3 p6 p1 p2 : Prop)
theorem file1_89541 : (((((p2 → p1) ∧ (p2 → p6)) ∧ ((p3 ∨ p6) ∧ (False → True))) → False) → ((((p7 ∨ True) → False) → False) ∨ (((True → False) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : (p7 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p7 p3 p4 p0 p1 : Prop)
theorem file1_89935 : (((((p4 ∧ p7) ∧ (False ∨ True)) ∧ ((p7 ∨ p1) → False)) → False) ∨ ((((p3 ∨ p3) → False) ∧ ((p7 → False) → (False ∨ p0))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          have assump_24 : (p7 ∨ p1) := by
            apply Or.inl
            exact assump_7
          let assump_20 := assump_3 assump_24
          apply False.elim assump_20


variable (p5 p4 p1 p3 p6 p7 : Prop)
theorem file1_90627 : (((((False → False) → False) → ((p5 → False) → (p6 ∧ True))) → False) → ((((p7 ∧ True) → False) → False) ∧ (((p6 ∧ p1) → False) → ((p5 ∨ p4) ∨ (p3 → False))))) := by
  intro assump_30
  apply And.intro
  intro assump_31
  have assump_79 : (((False → False) → False) → ((p5 → False) → (p6 ∧ True))) := by
    intro assump_37
    intro assump_38
    apply And.intro
    have assump_80 : (False → False) := by
      intro assump_44
      apply False.elim assump_44
    let assump_43 := assump_37 assump_80
    apply False.elim assump_43
    apply True.intro
  let assump_36 := assump_30 assump_79
  apply False.elim assump_36
  intro assump_53
  apply Or.inr
  intro assump_58
  have assump_81 : (((False → False) → False) → ((p5 → False) → (p6 ∧ True))) := by
    intro assump_63
    intro assump_64
    apply And.intro
    have assump_82 : (False → False) := by
      intro assump_70
      apply False.elim assump_70
    let assump_69 := assump_63 assump_82
    apply False.elim assump_69
    apply True.intro
  let assump_62 := assump_30 assump_81
  apply False.elim assump_62


variable (p1 p6 p5 p7 p3 p4 p0 : Prop)
theorem file1_91767 : (((((p3 → True) → False) → False) ∨ (((p7 ∧ p7) → False) ∧ ((False → False) ∧ (p0 ∧ False)))) ∨ ((((p7 ∧ p7) ∧ (p5 → False)) ∨ ((p5 → False) ∨ (True → False))) → (((p6 → False) ∨ (p4 ∧ p1)) ∧ ((p3 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_17
  have assump_25 : (p3 → True) := by
    intro assump_21
    apply True.intro
  let assump_20 := assump_17 assump_25
  apply False.elim assump_20


variable (p2 p3 : Prop)
theorem file1_92233 : (((((p2 → True) → False) ∧ ((False ∧ p3) ∧ (p2 ∧ p3))) ∨ (((True → False) → False) → False)) → False) := by
  intro assump_19
  cases assump_19
  case inl assump_20 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
  case inr assump_21 =>
    have assump_45 : ((True → False) → False) := by
      intro assump_35
      have assump_46 : True := by
        apply True.intro
      let assump_38 := assump_35 assump_46
      apply False.elim assump_38
    let assump_34 := assump_21 assump_45
    apply False.elim assump_34


variable (p5 p0 p3 p6 p7 p2 : Prop)
theorem file1_92989 : (((((p3 ∨ p2) ∨ (p0 → True)) → False) ∧ (((p7 ∨ p0) ∨ (False → False)) ∨ ((p6 → False) ∧ (p5 → p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_49 : ((p3 ∨ p2) ∨ (p0 → True)) := by
            apply Or.inr
            intro assump_16
            apply True.intro
          let assump_15 := assump_2 assump_49
          apply False.elim assump_15
        case inr assump_11 =>
          have assump_50 : ((p3 ∨ p2) ∨ (p0 → True)) := by
            apply Or.inr
            intro assump_24
            apply True.intro
          let assump_23 := assump_2 assump_50
          apply False.elim assump_23
      case inr assump_9 =>
        have assump_51 : ((p3 ∨ p2) ∨ (p0 → True)) := by
          apply Or.inr
          intro assump_32
          apply True.intro
        let assump_31 := assump_2 assump_51
        apply False.elim assump_31
    case inr assump_7 =>
      cases assump_7
      case intro assump_36 assump_37 =>
        have assump_52 : ((p3 ∨ p2) ∨ (p0 → True)) := by
          apply Or.inr
          intro assump_45
          apply True.intro
        let assump_44 := assump_2 assump_52
        apply False.elim assump_44


variable (p4 p3 p5 p1 p6 p0 p2 : Prop)
theorem file1_94397 : ((((((p1 ∨ p0) ∧ (p6 → p6)) ∧ ((p2 ∧ p1) → (False ∧ p5))) ∨ (((p4 → False) ∨ (p5 ∨ p6)) → ((p3 ∧ p5) → (True ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p1 ∨ p0) ∧ (p6 → p6)) ∧ ((p2 ∧ p1) → (False ∧ p5))) ∨ (((p4 → False) ∨ (p5 ∨ p6)) → ((p3 ∧ p5) → (True ∨ p4)))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        apply Or.inl
        apply True.intro
      case inr assump_14 =>
        cases assump_14
        case inl assump_17 =>
          apply Or.inl
          apply True.intro
        case inr assump_18 =>
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p0 p4 p2 p7 p1 p5 p3 : Prop)
theorem file1_95242 : (((((False → p1) ∧ (True ∧ p2)) ∧ ((p3 → p3) → False)) → (((p5 → False) → False) → ((p0 ∧ p7) ∧ (p1 ∧ p2)))) ∨ ((((True → p3) → False) → False) ∧ (((True → False) ∧ (False ∨ p4)) → False))) := by
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
        have assump_88 : (p3 → p3) := by
          intro assump_20
          exact assump_20
        let assump_19 := assump_6 assump_88
        apply False.elim assump_19
  cases assump_1
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_31
      case intro assump_34 assump_35 =>
        have assump_89 : (p3 → p3) := by
          intro assump_43
          exact assump_43
        let assump_42 := assump_29 assump_89
        apply False.elim assump_42
  apply And.intro
  cases assump_1
  case intro assump_51 assump_52 =>
    cases assump_51
    case intro assump_53 assump_54 =>
      cases assump_54
      case intro assump_57 assump_58 =>
        have assump_90 : (p3 → p3) := by
          intro assump_66
          exact assump_66
        let assump_65 := assump_52 assump_90
        apply False.elim assump_65
  cases assump_1
  case intro assump_74 assump_75 =>
    cases assump_74
    case intro assump_76 assump_77 =>
      cases assump_77
      case intro assump_80 assump_81 =>
        exact assump_81


variable (p5 p2 p3 p1 p7 : Prop)
theorem file1_96826 : (((((p1 → False) → False) ∨ ((p3 → False) → False)) ∧ (((p5 ∧ p1) ∧ (p7 → p7)) ∧ ((p5 ∨ p7) → (True → False)))) → ((((True ∧ p1) ∨ (p7 → False)) ∧ ((p3 → p1) → (p7 → False))) ∨ (((p2 → False) ∧ (p3 → False)) ∨ ((p5 ∧ p7) → False)))) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case inl assump_27 =>
      cases assump_26
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            apply And.intro
            apply True.intro
            exact assump_36
            intro assump_45
            intro assump_46
            have assump_87 : (p5 ∨ p7) := by
              apply Or.inl
              exact assump_35
            let assump_53 := assump_32 assump_87
            have assump_88 : True := by
              apply True.intro
            let assump_54 := assump_53 assump_88
            apply False.elim assump_54
    case inr assump_28 =>
      cases assump_26
      case intro assump_60 assump_61 =>
        cases assump_60
        case intro assump_62 assump_63 =>
          cases assump_62
          case intro assump_64 assump_65 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            apply And.intro
            apply True.intro
            exact assump_65
            intro assump_74
            intro assump_75
            have assump_89 : (p5 ∨ p7) := by
              apply Or.inl
              exact assump_64
            let assump_82 := assump_61 assump_89
            have assump_90 : True := by
              apply True.intro
            let assump_83 := assump_82 assump_90
            apply False.elim assump_83


variable (p6 p7 p1 p3 p0 p2 p4 p5 : Prop)
theorem file1_98729 : (((((p4 ∧ False) ∧ (p2 → p7)) → ((p3 ∧ p2) ∨ (True ∨ p3))) ∨ (((p7 → False) ∨ (p3 → p7)) → False)) ∨ ((((True ∧ p5) ∨ (p1 → p3)) → ((p1 ∧ p7) ∨ (False → False))) ∨ (((True → p3) ∨ (p0 → False)) ∧ ((p6 → False) ∧ (p4 → p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5


variable (p3 p2 p1 p4 p6 p5 p7 : Prop)
theorem file1_99209 : (((((p3 ∧ p4) ∨ (p1 ∧ p1)) → ((p7 → p5) ∧ (p3 → False))) → (((p4 → False) ∧ (p3 ∨ True)) → ((p6 ∨ p2) ∨ (p4 → p2)))) ∨ ((((p7 → p3) ∧ (p4 → p7)) ∨ ((p5 ∨ p5) → False)) → (((True ∧ p1) ∧ (p4 ∧ False)) → ((p5 ∨ p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      apply Or.inr
      intro assump_13
      have assump_37 : ((p3 ∧ p4) ∨ (p1 ∧ p1)) := by
        apply Or.inl
        apply And.intro
        exact assump_7
        exact assump_13
      let assump_17 := assump_1 assump_37
      let assump_18 := And.right assump_17
      have assump_38 : p3 := by
        exact assump_7
      let assump_20 := assump_18 assump_38
      apply False.elim assump_20
    case inr assump_8 =>
      apply Or.inr
      intro assump_28
      have assump_39 : p4 := by
        exact assump_28
      let assump_33 := assump_3 assump_39
      apply False.elim assump_33


variable (p7 p2 p1 p6 p4 p3 p0 p5 : Prop)
theorem file1_100249 : (((((p3 ∨ p5) ∨ (p4 ∧ p2)) ∧ ((False ∨ True) → False)) ∧ (((p3 → False) ∧ (p2 ∨ p1)) ∧ ((p3 ∧ p7) → (p4 → False)))) → ((((p7 → False) ∧ (p1 → p0)) ∨ ((p6 → p5) → False)) ∧ (((p2 → p3) ∧ (False ∨ p1)) ∧ ((p3 → p2) → (p2 → p2))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_17
              case inl assump_20 =>
                apply Or.inl
                apply And.intro
                intro assump_26
                have assump_477 : p3 := by
                  exact assump_8
                let assump_33 := assump_16 assump_477
                apply False.elim assump_33
                intro assump_37
                have assump_478 : p3 := by
                  exact assump_8
                let assump_43 := assump_16 assump_478
                apply False.elim assump_43
              case inr assump_21 =>
                apply Or.inl
                apply And.intro
                intro assump_51
                have assump_479 : p3 := by
                  exact assump_8
                let assump_58 := assump_16 assump_479
                apply False.elim assump_58
                intro assump_62
                have assump_480 : p3 := by
                  exact assump_8
                let assump_68 := assump_16 assump_480
                apply False.elim assump_68
        case inr assump_9 =>
          cases assump_3
          case intro assump_76 assump_77 =>
            cases assump_76
            case intro assump_78 assump_79 =>
              cases assump_79
              case inl assump_82 =>
                apply Or.inl
                apply And.intro
                intro assump_88
                have assump_481 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_95 := assump_5 assump_481
                apply False.elim assump_95
                intro assump_99
                have assump_482 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_106 := assump_5 assump_482
                apply False.elim assump_106
              case inr assump_83 =>
                apply Or.inl
                apply And.intro
                intro assump_114
                have assump_483 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_121 := assump_5 assump_483
                apply False.elim assump_121
                intro assump_125
                have assump_484 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_132 := assump_5 assump_484
                apply False.elim assump_132
      case inr assump_7 =>
        cases assump_7
        case intro assump_136 assump_137 =>
          cases assump_3
          case intro assump_144 assump_145 =>
            cases assump_144
            case intro assump_146 assump_147 =>
              cases assump_147
              case inl assump_150 =>
                apply Or.inl
                apply And.intro
                intro assump_156
                have assump_485 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_163 := assump_5 assump_485
                apply False.elim assump_163
                intro assump_167
                have assump_486 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_174 := assump_5 assump_486
                apply False.elim assump_174
              case inr assump_151 =>
                apply Or.inl
                apply And.intro
                intro assump_182
                have assump_487 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_189 := assump_5 assump_487
                apply False.elim assump_189
                intro assump_193
                have assump_488 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_200 := assump_5 assump_488
                apply False.elim assump_200
  apply And.intro
  apply And.intro
  intro assump_204
  cases assump_1
  case intro assump_207 assump_208 =>
    cases assump_207
    case intro assump_209 assump_210 =>
      cases assump_209
      case inl assump_211 =>
        cases assump_211
        case inl assump_213 =>
          cases assump_208
          case intro assump_219 assump_220 =>
            cases assump_219
            case intro assump_221 assump_222 =>
              cases assump_222
              case inl assump_225 =>
                exact assump_213
              case inr assump_226 =>
                exact assump_213
        case inr assump_214 =>
          cases assump_208
          case intro assump_239 assump_240 =>
            cases assump_239
            case intro assump_241 assump_242 =>
              cases assump_242
              case inl assump_245 =>
                have assump_489 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_254 := assump_210 assump_489
                apply False.elim assump_254
              case inr assump_246 =>
                have assump_490 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_265 := assump_210 assump_490
                apply False.elim assump_265
      case inr assump_212 =>
        cases assump_212
        case intro assump_269 assump_270 =>
          cases assump_208
          case intro assump_277 assump_278 =>
            cases assump_277
            case intro assump_279 assump_280 =>
              cases assump_280
              case inl assump_283 =>
                have assump_491 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_292 := assump_210 assump_491
                apply False.elim assump_292
              case inr assump_284 =>
                have assump_492 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_303 := assump_210 assump_492
                apply False.elim assump_303
  cases assump_1
  case intro assump_307 assump_308 =>
    cases assump_307
    case intro assump_309 assump_310 =>
      cases assump_309
      case inl assump_311 =>
        cases assump_311
        case inl assump_313 =>
          cases assump_308
          case intro assump_319 assump_320 =>
            cases assump_319
            case intro assump_321 assump_322 =>
              cases assump_322
              case inl assump_325 =>
                have assump_493 : p3 := by
                  exact assump_313
                let assump_333 := assump_321 assump_493
                apply False.elim assump_333
              case inr assump_326 =>
                apply Or.inr
                exact assump_326
        case inr assump_314 =>
          cases assump_308
          case intro assump_345 assump_346 =>
            cases assump_345
            case intro assump_347 assump_348 =>
              cases assump_348
              case inl assump_351 =>
                have assump_494 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_360 := assump_310 assump_494
                apply False.elim assump_360
              case inr assump_352 =>
                apply Or.inr
                exact assump_352
      case inr assump_312 =>
        cases assump_312
        case intro assump_368 assump_369 =>
          cases assump_308
          case intro assump_376 assump_377 =>
            cases assump_376
            case intro assump_378 assump_379 =>
              cases assump_379
              case inl assump_382 =>
                have assump_495 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_391 := assump_310 assump_495
                apply False.elim assump_391
              case inr assump_383 =>
                apply Or.inr
                exact assump_383
  intro assump_399
  intro assump_400
  cases assump_1
  case intro assump_405 assump_406 =>
    cases assump_405
    case intro assump_407 assump_408 =>
      cases assump_407
      case inl assump_409 =>
        cases assump_409
        case inl assump_411 =>
          cases assump_406
          case intro assump_417 assump_418 =>
            cases assump_417
            case intro assump_419 assump_420 =>
              cases assump_420
              case inl assump_423 =>
                exact assump_423
              case inr assump_424 =>
                exact assump_400
        case inr assump_412 =>
          cases assump_406
          case intro assump_437 assump_438 =>
            cases assump_437
            case intro assump_439 assump_440 =>
              cases assump_440
              case inl assump_443 =>
                exact assump_443
              case inr assump_444 =>
                exact assump_400
      case inr assump_410 =>
        cases assump_410
        case intro assump_453 assump_454 =>
          cases assump_406
          case intro assump_461 assump_462 =>
            cases assump_461
            case intro assump_463 assump_464 =>
              cases assump_464
              case inl assump_467 =>
                exact assump_467
              case inr assump_468 =>
                exact assump_454


variable (p3 p2 p0 : Prop)
theorem file1_110241 : ((((((False → True) → False) → False) ∨ (((p3 → False) ∧ (p3 ∧ p2)) ∧ ((p3 ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False → True) → False) → False) ∨ (((p3 → False) ∧ (p3 ∧ p2)) ∧ ((p3 ∧ p0) → False))) := by
    apply Or.inl
    intro assump_5
    have assump_17 : (False → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p0 p6 : Prop)
theorem file1_110796 : ((((((False ∨ p0) → False) → ((p7 → False) → False)) → (((p6 ∨ p6) ∨ (True → True)) → ((p7 ∨ True) ∧ (False ∨ True)))) → False) → False) := by
  intro assump_13
  have assump_54 : ((((False ∨ p0) → False) → ((p7 → False) → False)) → (((p6 ∨ p6) ∨ (True → True)) → ((p7 ∨ True) ∧ (False ∨ True)))) := by
    intro assump_17
    intro assump_18
    apply And.intro
    cases assump_18
    case inl assump_19 =>
      cases assump_19
      case inl assump_21 =>
        apply Or.inr
        apply True.intro
      case inr assump_22 =>
        apply Or.inr
        apply True.intro
    case inr assump_20 =>
      apply Or.inr
      apply True.intro
    cases assump_18
    case inl assump_35 =>
      cases assump_35
      case inl assump_37 =>
        apply Or.inr
        apply True.intro
      case inr assump_38 =>
        apply Or.inr
        apply True.intro
    case inr assump_36 =>
      apply Or.inr
      apply True.intro
  let assump_16 := assump_13 assump_54
  apply False.elim assump_16


variable (p6 p7 : Prop)
theorem file1_111843 : (((((False → p7) → False) → ((False ∧ True) ∨ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_22 : (((False → p7) → False) → ((False ∧ True) ∨ (p6 → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_23 : (False → p7) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p0 p2 p4 p5 p6 p1 : Prop)
theorem file1_112378 : (((((p5 ∨ p3) ∧ (p1 → p0)) → ((p2 ∨ True) ∨ (p5 → False))) → (((p4 ∧ p0) → (True ∨ p3)) → False)) → ((((False → False) ∧ (p5 → p4)) → ((p2 ∧ True) → (p4 ∨ p0))) → (((p6 ∧ p3) → (p4 ∧ p1)) ∧ ((True → False) → (p1 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_109 : (((p5 ∨ p3) ∧ (p1 → p0)) → ((p2 ∨ True) ∨ (p5 → False))) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_19 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
    let assump_14 := assump_1 assump_109
    have assump_110 : ((p4 ∧ p0) → (True ∨ p3)) := by
      intro assump_29
      cases assump_29
      case intro assump_30 assump_31 =>
        apply Or.inl
        apply True.intro
    let assump_28 := assump_14 assump_110
    apply False.elim assump_28
  cases assump_3
  case intro assump_39 assump_40 =>
    have assump_111 : (((p5 ∨ p3) ∧ (p1 → p0)) → ((p2 ∨ True) ∨ (p5 → False))) := by
      intro assump_50
      cases assump_50
      case intro assump_51 assump_52 =>
        cases assump_51
        case inl assump_53 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_54 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
    let assump_49 := assump_1 assump_111
    have assump_112 : ((p4 ∧ p0) → (True ∨ p3)) := by
      intro assump_64
      cases assump_64
      case intro assump_65 assump_66 =>
        apply Or.inl
        apply True.intro
    let assump_63 := assump_49 assump_112
    apply False.elim assump_63
  intro assump_74
  intro assump_75
  have assump_113 : (((p5 ∨ p3) ∧ (p1 → p0)) → ((p2 ∨ True) ∨ (p5 → False))) := by
    intro assump_85
    cases assump_85
    case intro assump_86 assump_87 =>
      cases assump_86
      case inl assump_88 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_89 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_84 := assump_1 assump_113
  have assump_114 : ((p4 ∧ p0) → (True ∨ p3)) := by
    intro assump_99
    cases assump_99
    case intro assump_100 assump_101 =>
      apply Or.inl
      apply True.intro
  let assump_98 := assump_84 assump_114
  apply False.elim assump_98


variable (p6 p3 p7 p4 p0 p1 : Prop)
theorem file1_114945 : (((((False ∧ p1) → False) → False) → False) ∨ ((((p6 ∧ p4) ∧ (True ∨ p0)) ∧ ((p4 ∧ p7) → (p1 ∨ p6))) ∨ (((True ∧ p3) → (p1 → False)) ∧ ((False ∨ p7) ∨ (p6 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ p1) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p4 p1 p7 p6 : Prop)
theorem file1_115424 : (((((p3 → True) → (p6 ∨ p4)) → ((p1 ∧ p1) ∧ (True → False))) → False) → ((((p3 → False) ∨ (p7 → False)) ∧ ((False ∧ p6) ∧ (p7 ∧ p4))) → False)) := by
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
          apply False.elim assump_11
    case inr assump_6 =>
      cases assump_4
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          apply False.elim assump_19


variable (p2 p1 p6 : Prop)
theorem file1_116105 : ((((((False → False) ∨ (p1 → p2)) ∨ ((p2 → False) → False)) ∨ (((p2 ∧ p6) → (True → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (p1 → p2)) ∨ ((p2 → False) → False)) ∨ (((p2 ∧ p6) → (True → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p7 p4 p1 p2 p5 p3 : Prop)
theorem file1_116601 : ((((((p3 ∧ True) → (p7 ∧ p3)) ∨ ((p0 ∧ p1) ∧ (False → False))) → (((True ∧ p7) ∧ (p0 → True)) ∨ ((p5 ∨ p1) → False))) ∧ ((((p2 ∧ p2) ∧ (True ∧ p4)) → ((p0 → p2) ∨ (True → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p2 ∧ p2) ∧ (True ∧ p4)) → ((p0 → p2) ∨ (True → p3))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply Or.inl
            intro assump_24
            exact assump_13
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


variable (p4 p2 p6 p3 p7 p5 p1 : Prop)
theorem file1_117385 : ((((((p2 → False) ∧ (p4 → False)) ∨ ((p5 ∨ False) → False)) → (((p6 → False) → (p7 → False)) ∧ ((False ∨ p4) → (p7 → False)))) ∧ ((((p2 ∨ p3) ∨ (p2 → p6)) → False) ∨ (((False → False) ∨ (p1 → p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_31 : ((p2 ∨ p3) ∨ (p2 → p6)) := by
        apply Or.inr
        intro assump_11
        have assump_32 : ((p2 ∨ p3) ∨ (p2 → p6)) := by
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_15 := assump_6 assump_32
        apply False.elim assump_15
      let assump_10 := assump_6 assump_31
      apply False.elim assump_10
    case inr assump_7 =>
      have assump_33 : ((False → False) ∨ (p1 → p1)) := by
        apply Or.inl
        intro assump_25
        apply False.elim assump_25
      let assump_24 := assump_7 assump_33
      apply False.elim assump_24


variable (p1 p7 p4 p3 p0 p6 : Prop)
theorem file1_118398 : (((((p6 → False) → False) → ((p1 ∧ p0) ∨ (False → False))) → False) → ((((True → p4) → False) ∨ ((p3 ∨ p7) ∧ (p6 → True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_55 : (((p6 → False) → False) → ((p1 ∧ p0) ∨ (False → False))) := by
      intro assump_10
      apply Or.inr
      intro assump_13
      apply False.elim assump_13
    let assump_9 := assump_1 assump_55
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case intro assump_19 assump_20 =>
      cases assump_19
      case inl assump_21 =>
        have assump_56 : (((p6 → False) → False) → ((p1 ∧ p0) ∨ (False → False))) := by
          intro assump_30
          apply Or.inr
          intro assump_33
          apply False.elim assump_33
        let assump_29 := assump_1 assump_56
        apply False.elim assump_29
      case inr assump_22 =>
        have assump_57 : (((p6 → False) → False) → ((p1 ∧ p0) ∨ (False → False))) := by
          intro assump_46
          apply Or.inr
          intro assump_49
          apply False.elim assump_49
        let assump_45 := assump_1 assump_57
        apply False.elim assump_45


variable (p5 p0 p2 p3 p6 p7 p1 : Prop)
theorem file1_119639 : ((((((p6 ∧ p5) ∧ (p3 ∧ p1)) → ((p7 → p6) → False)) ∧ (((p0 ∧ p3) ∨ (p3 → False)) → False)) ∧ ((((p2 → False) → (p2 → False)) ∧ ((p3 → p5) ∧ (p2 ∨ p3))) ∧ (((False → p7) → False) ∧ ((False → p0) → (p5 → False))))) → False) := by
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
            cases assump_17
            case inl assump_20 =>
              cases assump_11
              case intro assump_24 assump_25 =>
                have assump_62 : (False → p7) := by
                  intro assump_36
                  apply False.elim assump_36
                let assump_35 := assump_24 assump_62
                apply False.elim assump_35
            case inr assump_21 =>
              cases assump_11
              case intro assump_44 assump_45 =>
                have assump_63 : (False → p7) := by
                  intro assump_56
                  apply False.elim assump_56
                let assump_55 := assump_44 assump_63
                apply False.elim assump_55


variable (p2 p3 p5 p6 p1 p0 p7 p4 : Prop)
theorem file1_120959 : (((((p4 ∨ False) ∧ (p1 → p0)) ∧ ((True ∨ False) → (p5 ∧ p0))) ∨ (((p3 → False) → (p0 → p0)) ∧ ((p3 ∨ p3) ∧ (p7 → p2)))) ∨ ((((p5 → p7) → (False → p7)) → False) → (((p6 → False) → (p4 → False)) → ((p4 ∧ True) ∧ (False → p0))))) := by
  apply Or.inr
  intro assump_7
  intro assump_8
  apply And.intro
  apply And.intro
  have assump_24 : ((p5 → p7) → (False → p7)) := by
    intro assump_14
    intro assump_15
    apply False.elim assump_15
  let assump_13 := assump_7 assump_24
  apply False.elim assump_13
  apply True.intro
  intro assump_21
  apply False.elim assump_21


variable (p5 p3 p0 p7 p6 p1 p2 : Prop)
theorem file1_121596 : ((((((p6 ∨ p3) ∨ (p5 → False)) → False) → False) ∧ ((((p1 → False) ∧ (p3 ∧ False)) → ((p3 ∨ p7) ∧ (p2 → False))) ∧ (((p7 ∨ p0) → (True ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((p7 ∨ p0) → (True ∨ p0)) := by
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          apply Or.inl
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          apply True.intro
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p4 p2 p0 p5 p6 p1 : Prop)
theorem file1_122285 : ((((((p6 ∨ p2) ∨ (p4 → True)) → ((p0 → p2) ∧ (p1 ∧ p5))) → (((p6 ∧ p0) → (p2 → False)) → ((True ∨ p2) ∧ (p1 → p5)))) → False) → False) := by
  intro assump_5
  have assump_32 : ((((p6 ∨ p2) ∨ (p4 → True)) → ((p0 → p2) ∧ (p1 ∧ p5))) → (((p6 ∧ p0) → (p2 → False)) → ((True ∨ p2) ∧ (p1 → p5)))) := by
    intro assump_9
    intro assump_10
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_15
    have assump_33 : ((p6 ∨ p2) ∨ (p4 → True)) := by
      apply Or.inr
      intro assump_23
      apply True.intro
    let assump_22 := assump_9 assump_33
    let assump_24 := And.right assump_22
    let assump_26 := And.right assump_24
    exact assump_26
  let assump_8 := assump_5 assump_32
  apply False.elim assump_8


variable (p1 p7 p6 p0 : Prop)
theorem file1_123078 : ((((((p1 → p1) ∨ (p0 ∧ p6)) → False) → (((True ∧ p7) → (p6 ∨ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p1 → p1) ∨ (p0 ∧ p6)) → False) → (((True ∧ p7) → (p6 ∨ p0)) → False)) := by
    intro assump_5
    intro assump_6
    have assump_22 : ((p1 → p1) ∨ (p0 ∧ p6)) := by
      apply Or.inl
      intro assump_12
      exact assump_12
    let assump_11 := assump_5 assump_22
    apply False.elim assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p2 p4 p3 p6 p5 p1 : Prop)
theorem file1_123645 : (((((p2 ∨ p5) ∨ (p1 ∨ p2)) → False) ∨ (((p3 ∨ p0) → False) ∨ ((False → False) ∨ (p3 → False)))) → ((((p0 → False) ∧ (p6 → False)) → False) → (((False ∧ p4) → (False ∧ p4)) ∨ ((p1 ∨ p2) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
    cases assump_9
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
  case inr assump_6 =>
    cases assump_6
    case inl assump_18 =>
      apply Or.inl
      intro assump_22
      apply And.intro
      cases assump_22
      case intro assump_23 assump_24 =>
        apply False.elim assump_23
      cases assump_22
      case intro assump_27 assump_28 =>
        apply False.elim assump_27
    case inr assump_19 =>
      cases assump_19
      case inl assump_31 =>
        apply Or.inl
        intro assump_35
        apply And.intro
        cases assump_35
        case intro assump_36 assump_37 =>
          apply False.elim assump_36
        cases assump_35
        case intro assump_40 assump_41 =>
          apply False.elim assump_40
      case inr assump_32 =>
        apply Or.inl
        intro assump_46
        apply And.intro
        cases assump_46
        case intro assump_47 assump_48 =>
          apply False.elim assump_47
        cases assump_46
        case intro assump_51 assump_52 =>
          apply False.elim assump_51


variable (p5 p2 p7 p0 : Prop)
theorem file1_125191 : ((((((False → p7) → False) ∧ ((False → False) ∧ (p5 ∧ False))) → (((p0 → False) ∧ (False → False)) → ((p2 ∨ p7) ∨ (p0 → True)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((False → p7) → False) ∧ ((False → False) ∧ (p5 ∧ False))) → (((p0 → False) ∧ (False → False)) → ((p2 ∨ p7) ∨ (p0 → True)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p3 p0 p4 p5 p2 p7 : Prop)
theorem file1_125967 : (((((p4 → p0) → False) → False) ∨ (((True → p0) ∨ (p7 → False)) → ((p3 ∧ p3) → (True ∧ p3)))) → ((((False ∨ p3) ∧ (False → p4)) ∨ ((False ∧ p2) → (p2 ∧ p2))) ∨ (((False → p3) → (False ∨ p3)) → ((p7 ∧ p5) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
    cases assump_6
    case intro assump_11 assump_12 =>
      apply False.elim assump_11
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    intro assump_17
    apply And.intro
    cases assump_17
    case intro assump_18 assump_19 =>
      apply False.elim assump_18
    cases assump_17
    case intro assump_22 assump_23 =>
      apply False.elim assump_22


variable (p6 p2 p3 p1 p7 p4 : Prop)
theorem file1_126835 : (((((p3 ∨ p4) → (p2 → True)) → False) → (((True ∨ p7) → (p1 → False)) ∧ ((p1 → False) → (False → False)))) ∨ ((((p1 → False) → False) → False) → (((p4 → p3) → False) ∧ ((p6 → p3) ∧ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_32 : ((p3 ∨ p4) → (p2 → True)) := by
      intro assump_13
      intro assump_14
      apply True.intro
    let assump_12 := assump_1 assump_32
    apply False.elim assump_12
  case inr assump_7 =>
    have assump_33 : ((p3 ∨ p4) → (p2 → True)) := by
      intro assump_23
      intro assump_24
      apply True.intro
    let assump_22 := assump_1 assump_33
    apply False.elim assump_22
  intro assump_28
  intro assump_29
  apply False.elim assump_29


variable (p2 p6 p0 p7 p5 : Prop)
theorem file1_127690 : ((((((p6 ∨ p5) ∨ (p2 ∧ p2)) ∧ ((False → False) ∧ (p5 ∨ p2))) → False) ∧ ((((p2 → False) ∧ (p2 ∧ p5)) → ((p7 ∧ True) → False)) → (((p0 → False) ∧ (False ∨ False)) ∧ ((p0 ∧ p6) → (p5 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_43 : (((p2 → False) ∧ (p2 ∧ p5)) → ((p7 ∧ True) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_9
        case intro assump_17 assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            have assump_44 : p2 := by
              exact assump_21
            let assump_29 := assump_17 assump_44
            apply False.elim assump_29
    let assump_8 := assump_3 assump_43
    let assump_33 := And.left assump_8
    let assump_34 := And.right assump_33
    cases assump_34
    case inl assump_37 =>
      apply False.elim assump_37
    case inr assump_38 =>
      apply False.elim assump_38


variable (p1 p5 p6 p3 p0 p4 : Prop)
theorem file1_128759 : (((((False → False) ∨ (p5 ∧ True)) → ((True ∨ True) ∨ (False → p3))) ∨ (((p1 → False) ∧ (p3 ∧ p1)) ∨ ((p4 ∧ True) ∧ (p0 ∧ False)))) ∨ ((((p3 ∨ False) ∧ (p6 ∨ True)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p5 p0 p4 : Prop)
theorem file1_129283 : (((((p5 ∧ p4) ∧ (False → p0)) → ((False ∨ False) → (p4 → False))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p5 ∧ p4) ∧ (False → p0)) → ((False ∨ False) → (p4 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p0 p7 p3 p4 p6 p1 p5 p2 : Prop)
theorem file1_129804 : (((((p7 → p4) → False) → ((p5 → False) → (p3 → p6))) → (((p1 ∧ p3) ∨ (p7 ∨ p4)) → ((p0 ∧ p4) → (False → False)))) ∨ ((((p3 → p4) ∧ (False → False)) ∧ ((p0 → False) ∧ (p0 → p6))) ∨ (((p0 ∨ True) → (p2 ∧ p4)) ∨ ((p3 ∨ p0) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p2 p3 p4 p1 p0 p6 : Prop)
theorem file1_130213 : (((((p2 ∧ False) → False) ∨ ((p3 → p0) ∧ (p2 → p4))) → False) → ((((p4 → p6) → False) → ((p4 → False) → False)) ∧ (((p1 → False) ∧ (p2 → p2)) → False))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  intro assump_7
  have assump_45 : (((p2 ∧ False) → False) ∨ ((p3 → p0) ∧ (p2 → p4))) := by
    apply Or.inl
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply False.elim assump_17
  let assump_14 := assump_5 assump_45
  apply False.elim assump_14
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    have assump_46 : (((p2 ∧ False) → False) ∨ ((p3 → p0) ∧ (p2 → p4))) := by
      apply Or.inl
      intro assump_35
      cases assump_35
      case intro assump_36 assump_37 =>
        apply False.elim assump_37
    let assump_34 := assump_5 assump_46
    apply False.elim assump_34


variable (p4 p3 p1 p7 p2 p0 p5 : Prop)
theorem file1_131134 : (((((p3 → p7) ∨ (True → p3)) ∧ ((False → False) → False)) → False) ∨ ((((p0 ∨ p1) ∧ (p2 ∨ p4)) → False) → (((p2 ∨ p5) ∨ (False ∨ False)) ∨ ((p3 ∨ p3) → (p2 ∨ p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_28 : (False → False) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_28
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_29 : (False → False) := by
        intro assump_22
        apply False.elim assump_22
      let assump_21 := assump_3 assump_29
      apply False.elim assump_21


variable (p3 p2 p1 p4 p5 p0 : Prop)
theorem file1_131876 : ((((((True → False) → (p1 → False)) ∨ ((p2 → True) → (p4 → p5))) ∧ (((True ∨ p3) ∧ (p4 ∨ p0)) → ((p3 ∧ p4) → (p5 → p3)))) → False) → False) := by
  intro assump_5
  have assump_53 : ((((True → False) → (p1 → False)) ∨ ((p2 → True) → (p4 → p5))) ∧ (((True ∨ p3) ∧ (p4 ∨ p0)) → ((p3 ∧ p4) → (p5 → p3)))) := by
    apply And.intro
    apply Or.inl
    intro assump_9
    intro assump_10
    have assump_54 : True := by
      apply True.intro
    let assump_15 := assump_9 assump_54
    apply False.elim assump_15
    intro assump_19
    intro assump_20
    intro assump_21
    cases assump_20
    case intro assump_24 assump_25 =>
      cases assump_19
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          cases assump_31
          case inl assump_36 =>
            exact assump_24
          case inr assump_37 =>
            exact assump_24
        case inr assump_33 =>
          cases assump_31
          case inl assump_44 =>
            exact assump_33
          case inr assump_45 =>
            exact assump_33
  let assump_8 := assump_5 assump_53
  apply False.elim assump_8


variable (p4 p2 p7 : Prop)
theorem file1_133058 : (((((p2 ∨ p4) → (False → False)) ∨ ((p4 → False) ∧ (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p2 ∨ p4) → (False → False)) ∨ ((p4 → False) ∧ (p7 → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p0 p5 p2 p3 p6 : Prop)
theorem file1_133464 : (((((True ∨ p0) ∨ (True ∨ p7)) → False) → False) ∨ ((((p5 → False) ∨ (True → p7)) → False) → (((p3 → False) ∧ (p7 ∧ p6)) ∨ ((p5 ∨ True) ∧ (p2 ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∨ p0) ∨ (True ∨ p7)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p0 p6 p2 p5 p3 p4 p7 p1 : Prop)
theorem file1_133891 : (((((p7 → False) ∧ (p0 → p7)) ∨ ((p3 ∨ p3) ∧ (p7 → p7))) → (((False → p1) → False) → ((True → p6) ∧ (p2 ∨ p4)))) ∨ ((((False → False) ∧ (p4 → False)) → False) ∨ (((False → False) → (p6 → p6)) ∨ ((p5 ∧ p5) ∨ (True ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      have assump_104 : (False → p1) := by
        intro assump_19
        apply False.elim assump_19
      let assump_18 := assump_2 assump_104
      apply False.elim assump_18
  case inr assump_9 =>
    cases assump_9
    case intro assump_25 assump_26 =>
      cases assump_25
      case inl assump_27 =>
        have assump_105 : (False → p1) := by
          intro assump_36
          apply False.elim assump_36
        let assump_35 := assump_2 assump_105
        apply False.elim assump_35
      case inr assump_28 =>
        have assump_106 : (False → p1) := by
          intro assump_49
          apply False.elim assump_49
        let assump_48 := assump_2 assump_106
        apply False.elim assump_48
  cases assump_1
  case inl assump_57 =>
    cases assump_57
    case intro assump_59 assump_60 =>
      have assump_107 : (False → p1) := by
        intro assump_68
        apply False.elim assump_68
      let assump_67 := assump_2 assump_107
      apply False.elim assump_67
  case inr assump_58 =>
    cases assump_58
    case intro assump_74 assump_75 =>
      cases assump_74
      case inl assump_76 =>
        have assump_108 : (False → p1) := by
          intro assump_85
          apply False.elim assump_85
        let assump_84 := assump_2 assump_108
        apply False.elim assump_84
      case inr assump_77 =>
        have assump_109 : (False → p1) := by
          intro assump_98
          apply False.elim assump_98
        let assump_97 := assump_2 assump_109
        apply False.elim assump_97


variable (p5 p4 p6 p3 p1 p7 p0 p2 : Prop)
theorem file1_135892 : (((((p3 ∧ p6) → (False ∨ p7)) → ((p1 → p5) → (p2 → p7))) → False) → ((((False ∧ p2) ∨ (p3 ∧ p5)) ∨ ((p2 ∧ True) → (p7 → p0))) ∨ (((p7 → False) ∧ (p4 ∨ p5)) ∨ ((p2 → False) ∨ (p6 ∨ True))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    have assump_29 : (((p3 ∧ p6) → (False ∨ p7)) → ((p1 → p5) → (p2 → p7))) := by
      intro assump_17
      intro assump_18
      intro assump_19
      exact assump_5
    let assump_16 := assump_1 assump_29
    apply False.elim assump_16


variable (p7 p0 p6 p2 p1 p5 : Prop)
theorem file1_136520 : (((((False ∨ p6) ∨ (p7 ∧ p5)) ∨ ((p0 ∨ False) ∧ (False ∧ p5))) ∧ (((p1 ∧ p2) → (p7 ∧ p7)) ∧ ((p6 → False) → False))) ∨ ((((p2 → p2) ∧ (False → p2)) → False) → False)) := by
  apply Or.inr
  intro assump_1
  have assump_14 : ((p2 → p2) ∧ (False → p2)) := by
    apply And.intro
    intro assump_5
    exact assump_5
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p4 p1 p3 p5 p6 p0 p2 : Prop)
theorem file1_137015 : ((((((p6 → True) ∧ (p0 ∧ p1)) ∨ ((p1 → False) ∨ (p2 → p4))) ∧ (((False → p3) ∧ (p1 ∨ p5)) → False)) ∧ ((((p7 ∨ p6) ∨ (True ∧ p5)) → False) ∧ (((p6 → False) → (p2 ∧ False)) ∧ ((p4 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                have assump_75 : (p4 → True) := by
                  intro assump_31
                  apply True.intro
                let assump_30 := assump_25 assump_75
                apply False.elim assump_30
      case inr assump_7 =>
        cases assump_7
        case inl assump_35 =>
          cases assump_3
          case intro assump_41 assump_42 =>
            cases assump_42
            case intro assump_45 assump_46 =>
              have assump_76 : (p4 → True) := by
                intro assump_52
                apply True.intro
              let assump_51 := assump_46 assump_76
              apply False.elim assump_51
        case inr assump_36 =>
          cases assump_3
          case intro assump_60 assump_61 =>
            cases assump_61
            case intro assump_64 assump_65 =>
              have assump_77 : (p4 → True) := by
                intro assump_71
                apply True.intro
              let assump_70 := assump_65 assump_77
              apply False.elim assump_70


variable (p0 p5 p1 p7 p4 p6 p2 p3 : Prop)
theorem file1_138773 : (((((False ∧ True) → (p3 ∨ p2)) ∧ ((p6 ∨ False) ∧ (p5 → p4))) ∧ (((p4 → False) ∧ (p0 → p0)) ∧ ((p0 → False) ∨ (p1 ∧ p5)))) → ((((p4 → False) ∨ (True ∧ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_6
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_20
              case inl assump_27 =>
                have assump_82 : ((p4 → False) ∨ (True ∧ p7)) := by
                  apply Or.inl
                  intro assump_38
                  have assump_83 : p4 := by
                    exact assump_38
                  let assump_44 := assump_21 assump_83
                  apply False.elim assump_44
                let assump_37 := assump_2 assump_82
                apply False.elim assump_37
              case inr assump_28 =>
                cases assump_28
                case intro assump_51 assump_52 =>
                  have assump_84 : ((p4 → False) ∨ (True ∧ p7)) := by
                    apply Or.inl
                    intro assump_66
                    have assump_85 : p4 := by
                      exact assump_66
                    let assump_73 := assump_21 assump_85
                    apply False.elim assump_73
                  let assump_65 := assump_2 assump_84
                  apply False.elim assump_65
        case inr assump_14 =>
          apply False.elim assump_14


variable (p3 p0 p2 p5 p7 p4 p6 p1 : Prop)
theorem file1_140503 : (((((p0 ∨ p7) ∧ (False → p0)) ∧ ((p5 → False) ∨ (False ∧ p6))) ∨ (((p5 → False) ∨ (p1 → False)) ∨ ((p1 → False) ∨ (p3 → p3)))) → ((((p3 ∧ p4) → (p6 → p6)) → False) → (((p2 → p4) → False) → ((p2 ∧ p3) ∧ (True ∨ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_11
          case inl assump_20 =>
            have assump_342 : ((p3 ∧ p4) → (p6 → p6)) := by
              intro assump_28
              intro assump_29
              cases assump_28
              case intro assump_32 assump_33 =>
                exact assump_29
            let assump_27 := assump_2 assump_342
            apply False.elim assump_27
          case inr assump_21 =>
            cases assump_21
            case intro assump_41 assump_42 =>
              apply False.elim assump_41
        case inr assump_15 =>
          cases assump_11
          case inl assump_49 =>
            have assump_343 : ((p3 ∧ p4) → (p6 → p6)) := by
              intro assump_57
              intro assump_58
              cases assump_57
              case intro assump_61 assump_62 =>
                exact assump_58
            let assump_56 := assump_2 assump_343
            apply False.elim assump_56
          case inr assump_50 =>
            cases assump_50
            case intro assump_70 assump_71 =>
              apply False.elim assump_70
  case inr assump_9 =>
    cases assump_9
    case inl assump_74 =>
      cases assump_74
      case inl assump_76 =>
        have assump_344 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_82
          intro assump_83
          cases assump_82
          case intro assump_86 assump_87 =>
            exact assump_83
        let assump_81 := assump_2 assump_344
        apply False.elim assump_81
      case inr assump_77 =>
        have assump_345 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_99
          intro assump_100
          cases assump_99
          case intro assump_103 assump_104 =>
            exact assump_100
        let assump_98 := assump_2 assump_345
        apply False.elim assump_98
    case inr assump_75 =>
      cases assump_75
      case inl assump_112 =>
        have assump_346 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_118
          intro assump_119
          cases assump_118
          case intro assump_122 assump_123 =>
            exact assump_119
        let assump_117 := assump_2 assump_346
        apply False.elim assump_117
      case inr assump_113 =>
        have assump_347 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_135
          intro assump_136
          cases assump_135
          case intro assump_139 assump_140 =>
            exact assump_136
        let assump_134 := assump_2 assump_347
        apply False.elim assump_134
  cases assump_1
  case inl assump_152 =>
    cases assump_152
    case intro assump_154 assump_155 =>
      cases assump_154
      case intro assump_156 assump_157 =>
        cases assump_156
        case inl assump_158 =>
          cases assump_155
          case inl assump_164 =>
            have assump_348 : ((p3 ∧ p4) → (p6 → p6)) := by
              intro assump_172
              intro assump_173
              cases assump_172
              case intro assump_176 assump_177 =>
                exact assump_173
            let assump_171 := assump_2 assump_348
            apply False.elim assump_171
          case inr assump_165 =>
            cases assump_165
            case intro assump_185 assump_186 =>
              apply False.elim assump_185
        case inr assump_159 =>
          cases assump_155
          case inl assump_193 =>
            have assump_349 : ((p3 ∧ p4) → (p6 → p6)) := by
              intro assump_201
              intro assump_202
              cases assump_201
              case intro assump_205 assump_206 =>
                exact assump_202
            let assump_200 := assump_2 assump_349
            apply False.elim assump_200
          case inr assump_194 =>
            cases assump_194
            case intro assump_214 assump_215 =>
              apply False.elim assump_214
  case inr assump_153 =>
    cases assump_153
    case inl assump_218 =>
      cases assump_218
      case inl assump_220 =>
        have assump_350 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_226
          intro assump_227
          cases assump_226
          case intro assump_230 assump_231 =>
            exact assump_227
        let assump_225 := assump_2 assump_350
        apply False.elim assump_225
      case inr assump_221 =>
        have assump_351 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_243
          intro assump_244
          cases assump_243
          case intro assump_247 assump_248 =>
            exact assump_244
        let assump_242 := assump_2 assump_351
        apply False.elim assump_242
    case inr assump_219 =>
      cases assump_219
      case inl assump_256 =>
        have assump_352 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_262
          intro assump_263
          cases assump_262
          case intro assump_266 assump_267 =>
            exact assump_263
        let assump_261 := assump_2 assump_352
        apply False.elim assump_261
      case inr assump_257 =>
        have assump_353 : ((p3 ∧ p4) → (p6 → p6)) := by
          intro assump_279
          intro assump_280
          cases assump_279
          case intro assump_283 assump_284 =>
            exact assump_280
        let assump_278 := assump_2 assump_353
        apply False.elim assump_278
  cases assump_1
  case inl assump_296 =>
    cases assump_296
    case intro assump_298 assump_299 =>
      cases assump_298
      case intro assump_300 assump_301 =>
        cases assump_300
        case inl assump_302 =>
          cases assump_299
          case inl assump_308 =>
            apply Or.inl
            apply True.intro
          case inr assump_309 =>
            cases assump_309
            case intro assump_312 assump_313 =>
              apply False.elim assump_312
        case inr assump_303 =>
          cases assump_299
          case inl assump_320 =>
            apply Or.inl
            apply True.intro
          case inr assump_321 =>
            cases assump_321
            case intro assump_324 assump_325 =>
              apply False.elim assump_324
  case inr assump_297 =>
    cases assump_297
    case inl assump_328 =>
      cases assump_328
      case inl assump_330 =>
        apply Or.inl
        apply True.intro
      case inr assump_331 =>
        apply Or.inl
        apply True.intro
    case inr assump_329 =>
      cases assump_329
      case inl assump_336 =>
        apply Or.inl
        apply True.intro
      case inr assump_337 =>
        apply Or.inl
        apply True.intro


variable (p0 p6 p2 p7 p4 p1 : Prop)
theorem file1_147581 : (((((p4 ∨ p6) → (p1 → p7)) → ((p7 → False) → (p1 ∧ p4))) → (((False ∧ False) → False) → ((p0 ∧ p7) → (False → p0)))) ∨ ((((p1 ∨ p4) → False) → False) ∧ (((p2 → False) ∧ (p1 → p4)) → ((p0 ∨ False) ∧ (True → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p0 p6 p1 p4 : Prop)
theorem file1_147966 : (((((True → False) ∧ (p1 ∧ p6)) → ((p0 → p1) ∧ (False ∧ False))) → (((False ∧ p4) → False) → False)) → False) := by
  intro assump_1
  have assump_60 : (((True → False) ∧ (p1 ∧ p6)) → ((p0 → p1) ∧ (False ∧ False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        exact assump_13
    apply And.intro
    cases assump_5
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        have assump_61 : True := by
          apply True.intro
        let assump_31 := assump_19 assump_61
        apply False.elim assump_31
    cases assump_5
    case intro assump_35 assump_36 =>
      cases assump_36
      case intro assump_39 assump_40 =>
        have assump_62 : True := by
          apply True.intro
        let assump_47 := assump_35 assump_62
        apply False.elim assump_47
  let assump_4 := assump_1 assump_60
  have assump_63 : ((False ∧ p4) → False) := by
    intro assump_52
    cases assump_52
    case intro assump_53 assump_54 =>
      apply False.elim assump_53
  let assump_51 := assump_4 assump_63
  apply False.elim assump_51


variable (p2 p6 p7 p4 : Prop)
theorem file1_149248 : (((((p2 → p7) → (p2 → False)) → False) ∧ (((p6 → False) ∧ (False ∧ p6)) ∧ ((p4 → False) → (p2 → False)))) → False) := by
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


variable (p0 p6 p5 p1 p4 p2 p7 : Prop)
theorem file1_149716 : (((((p4 ∨ p6) → False) → ((p1 → p2) → (p2 → True))) ∨ (((p6 ∨ p6) ∨ (p7 → False)) → False)) ∨ ((((True → False) ∨ (p4 → False)) ∧ ((p7 ∧ p2) ∨ (p5 → False))) → (((p0 → False) ∨ (p6 ∨ p5)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro


variable (p2 p1 p3 p5 p7 : Prop)
theorem file1_150078 : ((((((False ∧ p2) → (p3 → p7)) ∨ ((p7 ∨ p5) → False)) ∨ (((p1 ∨ p3) → (p3 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∧ p2) → (p3 → p7)) ∨ ((p7 ∨ p5) → False)) ∨ (((p1 ∨ p3) → (p3 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p3 p0 p2 p7 p1 p5 p4 : Prop)
theorem file1_150621 : (((((True ∧ p2) → (p5 ∧ True)) ∨ ((p6 → p4) ∧ (p0 → True))) → (((p2 ∨ p3) → False) → ((p4 → True) → (p0 ∨ True)))) ∨ ((((p4 ∧ p5) ∨ (False ∧ p6)) → False) ∧ (((p3 ∨ p4) ∧ (p7 ∧ False)) ∨ ((p1 → False) ∧ (p7 ∧ p1))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_5
  case inl assump_12 =>
    apply Or.inr
    apply True.intro
  case inr assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      apply Or.inr
      apply True.intro


variable (p2 p1 p0 p5 : Prop)
theorem file1_151167 : ((((((p5 → p5) → False) ∨ ((p1 → False) ∧ (False → p1))) → (((p0 → False) ∨ (False ∨ p2)) → ((p1 ∨ True) ∨ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p5 → p5) → False) ∨ ((p1 → False) ∧ (False → p1))) → (((p0 → False) ∨ (False ∨ p2)) → ((p1 ∨ True) ∨ (p1 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case inl assump_11 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
    case inr assump_8 =>
      cases assump_8
      case inl assump_21 =>
        apply False.elim assump_21
      case inr assump_22 =>
        cases assump_5
        case inl assump_27 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_28 =>
          cases assump_28
          case intro assump_31 assump_32 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p1 p6 p2 p7 : Prop)
theorem file1_152403 : (((((p7 ∧ p2) ∧ (p7 ∨ p1)) → False) ∧ (((p2 → False) ∨ (p2 → p6)) ∧ ((False → p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_32 : (False → p1) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_7 assump_32
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_33 : (False → p1) := by
          intro assump_26
          apply False.elim assump_26
        let assump_25 := assump_7 assump_33
        apply False.elim assump_25


variable (p2 p7 p5 p3 p0 : Prop)
theorem file1_153138 : (((((False ∧ p0) → False) → False) ∧ (((p2 ∧ False) → False) ∨ ((p5 ∨ p3) ∧ (False ∧ False)))) → ((((p0 → p3) ∧ (p5 ∧ p2)) ∨ ((p3 → False) → False)) ∧ (((p0 ∧ False) → False) ∧ ((p7 → p5) ∧ (p3 ∧ p2))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inr
      intro assump_24
      have assump_166 : ((False ∧ p0) → False) := by
        intro assump_30
        cases assump_30
        case intro assump_31 assump_32 =>
          apply False.elim assump_31
      let assump_29 := assump_2 assump_166
      apply False.elim assump_29
    case inr assump_7 =>
      cases assump_7
      case intro assump_38 assump_39 =>
        cases assump_38
        case inl assump_40 =>
          cases assump_39
          case intro assump_44 assump_45 =>
            apply False.elim assump_44
        case inr assump_41 =>
          cases assump_39
          case intro assump_50 assump_51 =>
            apply False.elim assump_50
  apply And.intro
  intro assump_54
  cases assump_54
  case intro assump_55 assump_56 =>
    apply False.elim assump_56
  apply And.intro
  intro assump_61
  cases assump_1
  case intro assump_64 assump_65 =>
    cases assump_65
    case inl assump_68 =>
      have assump_167 : ((False ∧ p0) → False) := by
        intro assump_74
        cases assump_74
        case intro assump_75 assump_76 =>
          apply False.elim assump_75
      let assump_73 := assump_64 assump_167
      apply False.elim assump_73
    case inr assump_69 =>
      cases assump_69
      case intro assump_82 assump_83 =>
        cases assump_82
        case inl assump_84 =>
          cases assump_83
          case intro assump_88 assump_89 =>
            apply False.elim assump_88
        case inr assump_85 =>
          cases assump_83
          case intro assump_94 assump_95 =>
            apply False.elim assump_94
  apply And.intro
  cases assump_1
  case intro assump_98 assump_99 =>
    cases assump_99
    case inl assump_102 =>
      have assump_168 : ((False ∧ p0) → False) := by
        intro assump_108
        cases assump_108
        case intro assump_109 assump_110 =>
          apply False.elim assump_109
      let assump_107 := assump_98 assump_168
      apply False.elim assump_107
    case inr assump_103 =>
      cases assump_103
      case intro assump_116 assump_117 =>
        cases assump_116
        case inl assump_118 =>
          cases assump_117
          case intro assump_122 assump_123 =>
            apply False.elim assump_122
        case inr assump_119 =>
          cases assump_117
          case intro assump_128 assump_129 =>
            apply False.elim assump_128
  cases assump_1
  case intro assump_132 assump_133 =>
    cases assump_133
    case inl assump_136 =>
      have assump_169 : ((False ∧ p0) → False) := by
        intro assump_142
        cases assump_142
        case intro assump_143 assump_144 =>
          apply False.elim assump_143
      let assump_141 := assump_132 assump_169
      apply False.elim assump_141
    case inr assump_137 =>
      cases assump_137
      case intro assump_150 assump_151 =>
        cases assump_150
        case inl assump_152 =>
          cases assump_151
          case intro assump_156 assump_157 =>
            apply False.elim assump_156
        case inr assump_153 =>
          cases assump_151
          case intro assump_162 assump_163 =>
            apply False.elim assump_162


variable (p4 p7 p6 : Prop)
theorem file1_156677 : (((((p6 ∧ p4) ∧ (p6 ∨ p4)) → False) ∧ (((False ∧ p6) → False) → False)) → ((((p6 → p6) → (p7 → False)) → False) ∧ (((p4 → False) ∧ (True ∨ p7)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_61 : ((False ∧ p6) → False) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_11 := assump_6 assump_61
    apply False.elim assump_11
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_22
    case inl assump_25 =>
      cases assump_1
      case intro assump_29 assump_30 =>
        have assump_62 : ((False ∧ p6) → False) := by
          intro assump_36
          cases assump_36
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
        let assump_35 := assump_30 assump_62
        apply False.elim assump_35
    case inr assump_26 =>
      cases assump_1
      case intro assump_46 assump_47 =>
        have assump_63 : ((False ∧ p6) → False) := by
          intro assump_53
          cases assump_53
          case intro assump_54 assump_55 =>
            apply False.elim assump_54
        let assump_52 := assump_47 assump_63
        apply False.elim assump_52


variable (p4 p2 p0 p6 p1 p5 : Prop)
theorem file1_158045 : (((((False → p6) ∨ (False → False)) ∨ ((p5 → p1) ∨ (False ∨ p2))) → False) → ((((p0 → False) → (True → False)) → False) → (((False → False) → (True → False)) ∨ ((p4 ∧ p4) ∧ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  have assump_21 : (((False → p6) ∨ (False → False)) ∨ ((p5 → p1) ∨ (False ∨ p2))) := by
    apply Or.inl
    apply Or.inl
    intro assump_15
    apply False.elim assump_15
  let assump_14 := assump_1 assump_21
  apply False.elim assump_14


variable (p6 p1 p7 p4 p2 p5 : Prop)
theorem file1_158625 : (((((p5 ∨ True) → False) → ((False ∧ p4) ∨ (p2 → p1))) ∧ (((p5 ∧ False) → (p2 ∧ p6)) ∨ ((p7 → p2) ∧ (p5 → p6)))) ∨ ((((p1 → False) ∧ (p4 ∧ p2)) → ((p6 → False) → False)) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply Or.inr
  intro assump_4
  have assump_25 : (p5 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_8 := assump_1 assump_25
  apply False.elim assump_8
  apply Or.inl
  intro assump_12
  apply And.intro
  cases assump_12
  case intro assump_13 assump_14 =>
    apply False.elim assump_14
  cases assump_12
  case intro assump_19 assump_20 =>
    apply False.elim assump_20


variable (p0 p4 p1 p6 p3 p7 p2 : Prop)
theorem file1_159317 : (((((p7 ∨ p3) → (p7 ∧ False)) ∧ ((p6 ∧ p0) → (p3 → p6))) ∧ (((p3 ∧ p3) ∧ (p1 → p0)) ∧ ((p0 ∧ p4) ∧ (p1 ∨ p2)))) → False) := by
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
            cases assump_11
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                cases assump_23
                case inl assump_30 =>
                  have assump_63 : (p7 ∨ p3) := by
                    apply Or.inr
                    exact assump_15
                  let assump_42 := assump_4 assump_63
                  let assump_43 := And.right assump_42
                  apply False.elim assump_43
                case inr assump_31 =>
                  have assump_64 : (p7 ∨ p3) := by
                    apply Or.inr
                    exact assump_15
                  let assump_57 := assump_4 assump_64
                  let assump_58 := And.right assump_57
                  apply False.elim assump_58


variable (p7 p5 : Prop)
theorem file1_160620 : ((((((p5 → True) → (p7 → False)) ∧ ((False → False) → (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p5 → True) → (p7 → False)) ∧ ((False → False) → (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_24 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_24
      have assump_25 : True := by
        apply True.intro
      let assump_16 := assump_12 assump_25
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p0 p1 p4 p7 p3 p2 p5 : Prop)
theorem file1_161327 : ((((((True ∨ p7) → (p3 → False)) → ((p0 ∧ p4) ∨ (p3 → True))) → False) ∧ ((((p1 → False) ∨ (True ∧ p4)) → ((p1 ∧ p2) ∧ (p1 → False))) ∧ (((p5 ∧ p1) ∨ (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((p5 ∧ p1) ∨ (False → False)) := by
        apply Or.inr
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12
