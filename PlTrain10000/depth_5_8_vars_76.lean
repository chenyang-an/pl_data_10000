variable (p2 p3 p4 p5 p1 p0 : Prop)
theorem file76_44 : ((((((p2 ∧ False) → False) → ((p5 ∨ p4) → (p4 ∨ p3))) → (((p3 ∨ False) ∨ (p1 ∧ p0)) ∨ ((p4 → True) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p2 ∧ False) → False) → ((p5 ∨ p4) → (p4 ∨ p3))) → (((p3 ∨ False) ∨ (p1 ∧ p0)) ∨ ((p4 → True) ∨ (p3 → False)))) := by
    intro assump_5
    apply Or.inr
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p7 p1 p4 p3 p6 : Prop)
theorem file76_560 : ((((((p6 → False) → (p6 → False)) ∨ ((p3 → p6) ∨ (False ∨ p5))) → (((p4 → False) → False) ∧ ((False → False) ∨ (True ∨ True)))) ∧ ((((p6 → False) ∧ (True → True)) → ((p1 ∨ p7) ∨ (p7 → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_37 : (((p6 → False) ∧ (True → True)) → ((p1 ∨ p7) ∨ (p7 → p1))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        intro assump_16
        have assump_38 : (((p6 → False) ∧ (True → True)) → ((p1 ∨ p7) ∨ (p7 → p1))) := by
          intro assump_24
          cases assump_24
          case intro assump_25 assump_26 =>
            apply Or.inl
            apply Or.inr
            exact assump_16
        let assump_23 := assump_3 assump_38
        apply False.elim assump_23
    let assump_8 := assump_3 assump_37
    apply False.elim assump_8


variable (p7 p0 p4 p5 p2 p3 p6 : Prop)
theorem file76_1531 : (((((p2 → p2) → (p7 ∧ False)) → ((True ∧ False) → (False ∧ p4))) ∨ (((False ∨ p7) ∨ (p2 → False)) → ((p3 ∨ p3) → (p2 → p6)))) ∨ ((((p5 ∧ p0) ∧ (p3 ∧ p7)) → ((p3 ∧ p2) → (p4 ∧ False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    apply False.elim assump_10


variable (p2 p6 p7 p4 p5 p1 p0 : Prop)
theorem file76_2040 : (((((p7 → p2) → (p2 → True)) ∨ ((p5 → p0) → False)) ∨ (((False ∧ False) → (p1 → True)) ∧ ((p6 ∨ p7) ∧ (False → False)))) ∨ ((((p4 ∧ p4) → (p4 ∨ p4)) → ((p1 → p2) ∨ (p4 → False))) ∨ (((p4 → False) ∧ (p1 ∨ p7)) ∨ ((False → False) ∨ (p2 ∨ p1))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro


variable (p6 p5 p7 p1 p0 : Prop)
theorem file76_2445 : (((((p6 → False) ∧ (p1 ∧ False)) ∧ ((p7 ∧ p7) → False)) ∧ (((p0 → False) ∨ (p5 → False)) ∧ ((p7 → p0) → (False → False)))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          apply False.elim assump_25


variable (p2 p7 p5 p3 p0 : Prop)
theorem file76_2935 : (((((p7 → False) → (p5 ∨ True)) ∨ ((p0 → p2) → (p5 → p3))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p7 → False) → (p5 ∨ True)) ∨ ((p0 → p2) → (p5 → p3))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p4 p6 : Prop)
theorem file76_3307 : ((((((False → False) → False) → ((True → False) → False)) ∨ (((True ∨ p2) → (p6 ∧ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → False) → False) → ((True → False) → False)) ∨ (((True ∨ p2) → (p6 ∧ p4)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_22 : (False → False) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_22
    apply False.elim assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p2 p1 p3 : Prop)
theorem file76_3908 : ((((((p2 → True) ∧ (p4 ∧ False)) ∧ ((p2 → False) → (p1 ∧ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p2 → True) ∧ (p4 ∧ False)) ∧ ((p2 → False) → (p1 ∧ p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p4 p7 p0 p5 p6 : Prop)
theorem file76_4476 : ((((((p1 → False) ∧ (p4 → False)) ∨ ((True ∨ p7) ∧ (p0 ∧ p0))) ∧ (((True ∧ p6) → (p0 ∧ p1)) ∧ ((p6 → p4) → False))) ∧ ((((p4 → True) → (p6 ∧ True)) ∧ ((True → False) ∧ (p4 ∨ p5))) ∧ (((p6 ∧ p6) ∨ (p0 → False)) ∨ ((p4 → p0) ∧ (p5 ∨ p6))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_9
          case intro assump_18 assump_19 =>
            cases assump_7
            case intro assump_24 assump_25 =>
              cases assump_24
              case intro assump_26 assump_27 =>
                cases assump_27
                case intro assump_30 assump_31 =>
                  cases assump_31
                  case inl assump_34 =>
                    cases assump_25
                    case inl assump_38 =>
                      cases assump_38
                      case inl assump_40 =>
                        cases assump_40
                        case intro assump_42 assump_43 =>
                          have assump_396 : True := by
                            apply True.intro
                          let assump_51 := assump_30 assump_396
                          apply False.elim assump_51
                      case inr assump_41 =>
                        have assump_397 : True := by
                          apply True.intro
                        let assump_59 := assump_30 assump_397
                        apply False.elim assump_59
                    case inr assump_39 =>
                      cases assump_39
                      case intro assump_63 assump_64 =>
                        cases assump_64
                        case inl assump_67 =>
                          have assump_398 : True := by
                            apply True.intro
                          let assump_75 := assump_30 assump_398
                          apply False.elim assump_75
                        case inr assump_68 =>
                          have assump_399 : True := by
                            apply True.intro
                          let assump_85 := assump_30 assump_399
                          apply False.elim assump_85
                  case inr assump_35 =>
                    cases assump_25
                    case inl assump_91 =>
                      cases assump_91
                      case inl assump_93 =>
                        cases assump_93
                        case intro assump_95 assump_96 =>
                          have assump_400 : True := by
                            apply True.intro
                          let assump_104 := assump_30 assump_400
                          apply False.elim assump_104
                      case inr assump_94 =>
                        have assump_401 : True := by
                          apply True.intro
                        let assump_112 := assump_30 assump_401
                        apply False.elim assump_112
                    case inr assump_92 =>
                      cases assump_92
                      case intro assump_116 assump_117 =>
                        cases assump_117
                        case inl assump_120 =>
                          have assump_402 : True := by
                            apply True.intro
                          let assump_127 := assump_30 assump_402
                          apply False.elim assump_127
                        case inr assump_121 =>
                          have assump_403 : True := by
                            apply True.intro
                          let assump_136 := assump_30 assump_403
                          apply False.elim assump_136
      case inr assump_11 =>
        cases assump_11
        case intro assump_140 assump_141 =>
          cases assump_140
          case inl assump_142 =>
            cases assump_141
            case intro assump_146 assump_147 =>
              cases assump_9
              case intro assump_152 assump_153 =>
                cases assump_7
                case intro assump_158 assump_159 =>
                  cases assump_158
                  case intro assump_160 assump_161 =>
                    cases assump_161
                    case intro assump_164 assump_165 =>
                      cases assump_165
                      case inl assump_168 =>
                        cases assump_159
                        case inl assump_172 =>
                          cases assump_172
                          case inl assump_174 =>
                            cases assump_174
                            case intro assump_176 assump_177 =>
                              have assump_404 : True := by
                                apply True.intro
                              let assump_185 := assump_164 assump_404
                              apply False.elim assump_185
                          case inr assump_175 =>
                            have assump_405 : p0 := by
                              exact assump_147
                            let assump_191 := assump_175 assump_405
                            apply False.elim assump_191
                        case inr assump_173 =>
                          cases assump_173
                          case intro assump_195 assump_196 =>
                            cases assump_196
                            case inl assump_199 =>
                              have assump_406 : True := by
                                apply True.intro
                              let assump_207 := assump_164 assump_406
                              apply False.elim assump_207
                            case inr assump_200 =>
                              have assump_407 : True := by
                                apply True.intro
                              let assump_217 := assump_164 assump_407
                              apply False.elim assump_217
                      case inr assump_169 =>
                        cases assump_159
                        case inl assump_223 =>
                          cases assump_223
                          case inl assump_225 =>
                            cases assump_225
                            case intro assump_227 assump_228 =>
                              have assump_408 : True := by
                                apply True.intro
                              let assump_236 := assump_164 assump_408
                              apply False.elim assump_236
                          case inr assump_226 =>
                            have assump_409 : p0 := by
                              exact assump_147
                            let assump_242 := assump_226 assump_409
                            apply False.elim assump_242
                        case inr assump_224 =>
                          cases assump_224
                          case intro assump_246 assump_247 =>
                            cases assump_247
                            case inl assump_250 =>
                              have assump_410 : True := by
                                apply True.intro
                              let assump_257 := assump_164 assump_410
                              apply False.elim assump_257
                            case inr assump_251 =>
                              have assump_411 : True := by
                                apply True.intro
                              let assump_266 := assump_164 assump_411
                              apply False.elim assump_266
          case inr assump_143 =>
            cases assump_141
            case intro assump_272 assump_273 =>
              cases assump_9
              case intro assump_278 assump_279 =>
                cases assump_7
                case intro assump_284 assump_285 =>
                  cases assump_284
                  case intro assump_286 assump_287 =>
                    cases assump_287
                    case intro assump_290 assump_291 =>
                      cases assump_291
                      case inl assump_294 =>
                        cases assump_285
                        case inl assump_298 =>
                          cases assump_298
                          case inl assump_300 =>
                            cases assump_300
                            case intro assump_302 assump_303 =>
                              have assump_412 : True := by
                                apply True.intro
                              let assump_311 := assump_290 assump_412
                              apply False.elim assump_311
                          case inr assump_301 =>
                            have assump_413 : p0 := by
                              exact assump_273
                            let assump_317 := assump_301 assump_413
                            apply False.elim assump_317
                        case inr assump_299 =>
                          cases assump_299
                          case intro assump_321 assump_322 =>
                            cases assump_322
                            case inl assump_325 =>
                              have assump_414 : True := by
                                apply True.intro
                              let assump_333 := assump_290 assump_414
                              apply False.elim assump_333
                            case inr assump_326 =>
                              have assump_415 : True := by
                                apply True.intro
                              let assump_343 := assump_290 assump_415
                              apply False.elim assump_343
                      case inr assump_295 =>
                        cases assump_285
                        case inl assump_349 =>
                          cases assump_349
                          case inl assump_351 =>
                            cases assump_351
                            case intro assump_353 assump_354 =>
                              have assump_416 : True := by
                                apply True.intro
                              let assump_362 := assump_290 assump_416
                              apply False.elim assump_362
                          case inr assump_352 =>
                            have assump_417 : p0 := by
                              exact assump_273
                            let assump_368 := assump_352 assump_417
                            apply False.elim assump_368
                        case inr assump_350 =>
                          cases assump_350
                          case intro assump_372 assump_373 =>
                            cases assump_373
                            case inl assump_376 =>
                              have assump_418 : True := by
                                apply True.intro
                              let assump_383 := assump_290 assump_418
                              apply False.elim assump_383
                            case inr assump_377 =>
                              have assump_419 : True := by
                                apply True.intro
                              let assump_392 := assump_290 assump_419
                              apply False.elim assump_392


variable (p5 p3 p7 : Prop)
theorem file76_15881 : (((((True ∨ False) ∧ (False → p5)) ∧ ((True → False) → (p3 → p7))) → False) → False) := by
  intro assump_1
  have assump_21 : (((True ∨ False) ∧ (False → p5)) ∧ ((True → False) → (p3 → p7))) := by
    apply And.intro
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    intro assump_9
    have assump_22 : True := by
      apply True.intro
    let assump_14 := assump_8 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p3 p5 p0 p4 p2 p7 : Prop)
theorem file76_16498 : (((((p5 → True) ∨ (p4 → p3)) ∨ ((p3 ∧ p3) → (p7 → p2))) ∨ (((False ∨ p4) ∨ (p4 ∨ p0)) → False)) ∨ ((((True → False) ∨ (p3 → False)) → ((p7 ∧ False) ∨ (p0 ∨ p1))) ∨ (((p4 → p1) ∧ (p7 → p3)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p5 p1 p0 p7 p2 p4 p3 : Prop)
theorem file76_16863 : ((((((True ∧ False) ∧ (p4 → p5)) ∧ ((True → False) → (p4 ∧ p5))) ∧ (((p1 ∧ p4) ∨ (p0 → p7)) → ((p7 → p4) ∨ (p2 ∧ p5)))) ∧ ((((p1 ∨ p1) ∨ (False → p3)) ∨ ((p0 ∨ p1) ∨ (False ∧ False))) → (((False → p2) ∨ (False ∨ p0)) ∨ ((p5 ∧ p3) → False)))) → False) := by
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
            apply False.elim assump_11


variable (p4 p6 p3 : Prop)
theorem file76_17524 : (((((True ∨ False) ∨ (False ∨ True)) ∨ ((p4 ∨ True) → (p6 → p3))) ∧ (((False ∧ p6) → False) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          have assump_65 : ((False ∧ p6) → False) := by
            intro assump_25
            cases assump_25
            case intro assump_26 assump_27 =>
              apply False.elim assump_26
          let assump_24 := assump_13 assump_65
          apply False.elim assump_24
        case inr assump_19 =>
          apply False.elim assump_19
      case inr assump_17 =>
        cases assump_17
        case inl assump_35 =>
          apply False.elim assump_35
        case inr assump_36 =>
          have assump_66 : ((False ∧ p6) → False) := by
            intro assump_44
            cases assump_44
            case intro assump_45 assump_46 =>
              apply False.elim assump_45
          let assump_43 := assump_13 assump_66
          apply False.elim assump_43
    case inr assump_15 =>
      have assump_67 : ((False ∧ p6) → False) := by
        intro assump_57
        cases assump_57
        case intro assump_58 assump_59 =>
          apply False.elim assump_58
      let assump_56 := assump_13 assump_67
      apply False.elim assump_56


variable (p7 p5 p4 p0 p1 p2 p6 : Prop)
theorem file76_18989 : (((((p5 ∨ p7) ∨ (p6 ∧ True)) → False) ∧ (((True → p2) ∧ (True → False)) ∨ ((p4 → False) ∧ (False ∧ p5)))) → ((((False ∧ p1) ∨ (p0 → False)) ∨ ((p1 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
    case inr assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            have assump_63 : True := by
              apply True.intro
            let assump_25 := assump_20 assump_63
            apply False.elim assump_25
        case inr assump_18 =>
          cases assump_18
          case intro assump_29 assump_30 =>
            cases assump_30
            case intro assump_33 assump_34 =>
              apply False.elim assump_33
  case inr assump_4 =>
    cases assump_1
    case intro assump_39 assump_40 =>
      cases assump_40
      case inl assump_43 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          have assump_64 : True := by
            apply True.intro
          let assump_51 := assump_46 assump_64
          apply False.elim assump_51
      case inr assump_44 =>
        cases assump_44
        case intro assump_55 assump_56 =>
          cases assump_56
          case intro assump_59 assump_60 =>
            apply False.elim assump_59


variable (p3 p2 p0 p1 p4 p5 : Prop)
theorem file76_20576 : (((((p0 → p5) → (False → False)) → False) → (((p3 → False) → False) ∧ ((p0 ∧ p1) ∧ (False ∧ False)))) ∨ ((((True ∧ p5) ∨ (p4 ∨ p2)) → ((p4 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_55 : ((p0 → p5) → (False → False)) := by
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_55
  apply False.elim assump_7
  apply And.intro
  apply And.intro
  have assump_56 : ((p0 → p5) → (False → False)) := by
    intro assump_18
    intro assump_19
    apply False.elim assump_19
  let assump_17 := assump_1 assump_56
  apply False.elim assump_17
  have assump_57 : ((p0 → p5) → (False → False)) := by
    intro assump_28
    intro assump_29
    apply False.elim assump_29
  let assump_27 := assump_1 assump_57
  apply False.elim assump_27
  apply And.intro
  have assump_58 : ((p0 → p5) → (False → False)) := by
    intro assump_38
    intro assump_39
    apply False.elim assump_39
  let assump_37 := assump_1 assump_58
  apply False.elim assump_37
  have assump_59 : ((p0 → p5) → (False → False)) := by
    intro assump_48
    intro assump_49
    apply False.elim assump_49
  let assump_47 := assump_1 assump_59
  apply False.elim assump_47


variable (p6 p2 p1 p0 p5 p7 p4 : Prop)
theorem file76_21894 : (((((p5 ∨ p1) → (p6 → False)) → False) → False) → ((((p4 ∨ p0) → (p0 ∨ p0)) ∧ ((False ∨ p7) ∧ (p2 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply False.elim assump_16


variable (p7 p3 p4 : Prop)
theorem file76_22422 : (((((p7 → True) → False) → ((p4 → False) ∨ (p3 → p3))) → False) → False) := by
  intro assump_1
  have assump_20 : (((p7 → True) → False) → ((p4 → False) ∨ (p3 → p3))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_21 : (p7 → True) := by
      intro assump_13
      apply True.intro
    let assump_12 := assump_5 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p6 p4 p3 p7 p0 p2 p5 : Prop)
theorem file76_22934 : ((((((p4 → False) ∧ (False ∧ p4)) ∨ ((True → False) ∧ (p3 → p3))) → False) → ((((p2 → True) → False) → ((p4 ∨ p7) → (p6 ∧ p5))) → (((p0 ∧ p0) → False) ∧ ((False ∧ p2) ∧ (p4 ∧ p7))))) → False) := by
  intro assump_1
  have assump_77 : ((((p4 → False) ∧ (False ∧ p4)) ∨ ((True → False) ∧ (p3 → p3))) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
    case inr assump_7 =>
      cases assump_7
      case intro assump_16 assump_17 =>
        have assump_78 : True := by
          apply True.intro
        let assump_23 := assump_16 assump_78
        apply False.elim assump_23
  let assump_4 := assump_1 assump_77
  have assump_79 : (((p2 → True) → False) → ((p4 ∨ p7) → (p6 ∧ p5))) := by
    intro assump_28
    intro assump_29
    apply And.intro
    cases assump_29
    case inl assump_30 =>
      have assump_80 : (p2 → True) := by
        intro assump_37
        apply True.intro
      let assump_36 := assump_28 assump_80
      apply False.elim assump_36
    case inr assump_31 =>
      have assump_81 : (p2 → True) := by
        intro assump_46
        apply True.intro
      let assump_45 := assump_28 assump_81
      apply False.elim assump_45
    cases assump_29
    case inl assump_50 =>
      have assump_82 : (p2 → True) := by
        intro assump_57
        apply True.intro
      let assump_56 := assump_28 assump_82
      apply False.elim assump_56
    case inr assump_51 =>
      have assump_83 : (p2 → True) := by
        intro assump_66
        apply True.intro
      let assump_65 := assump_28 assump_83
      apply False.elim assump_65
  let assump_27 := assump_4 assump_79
  let assump_70 := And.right assump_27
  let assump_72 := And.left assump_70
  let assump_73 := And.left assump_72
  apply False.elim assump_73


variable (p4 p7 p5 p3 p2 p0 p6 : Prop)
theorem file76_24925 : (((((p0 ∨ True) → False) → ((False ∧ True) ∧ (p2 → True))) ∧ (((p3 → False) → (False → p4)) ∧ ((p2 ∨ False) → False))) → ((((False ∧ p0) ∧ (p6 → False)) ∧ ((p2 → False) ∧ (True ∧ p6))) → (((False → p7) → False) ∧ ((True → p6) ∧ (p5 → p6))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  apply And.intro
  intro assump_14
  cases assump_2
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        apply False.elim assump_21
  intro assump_25
  cases assump_2
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        apply False.elim assump_32


variable (p4 p1 p2 p7 p6 p3 : Prop)
theorem file76_25974 : (((((False ∨ p7) ∨ (p7 → False)) → False) → False) ∨ ((((p1 ∧ p3) ∨ (p6 → False)) → False) ∧ (((p4 → p2) → False) → ((p2 → False) ∨ (p2 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  have assump_16 : ((False ∨ p7) ∨ (p7 → False)) := by
    apply Or.inr
    intro assump_5
    have assump_17 : ((False ∨ p7) ∨ (p7 → False)) := by
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p1 p3 p7 p0 p6 : Prop)
theorem file76_26559 : ((((((p6 ∧ p6) ∧ (p7 ∧ p7)) → ((p7 ∧ p7) ∨ (p3 → p1))) → False) ∨ ((((p3 ∧ p5) ∧ (p3 → False)) → ((p3 ∨ p0) → (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_70 : (((p6 ∧ p6) ∧ (p7 ∧ p7)) → ((p7 ∧ p7) ∨ (p3 → p1))) := by
      intro assump_7
      cases assump_7
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply Or.inl
            apply And.intro
            exact assump_17
            exact assump_17
    let assump_6 := assump_2 assump_70
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_71 : (((p3 ∧ p5) ∧ (p3 → False)) → ((p3 ∨ p0) → (p3 → False))) := by
      intro assump_28
      intro assump_29
      intro assump_30
      cases assump_29
      case inl assump_33 =>
        cases assump_28
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            have assump_72 : p3 := by
              exact assump_39
            let assump_47 := assump_38 assump_72
            apply False.elim assump_47
      case inr assump_34 =>
        cases assump_28
        case intro assump_53 assump_54 =>
          cases assump_53
          case intro assump_55 assump_56 =>
            have assump_73 : p3 := by
              exact assump_55
            let assump_63 := assump_54 assump_73
            apply False.elim assump_63
    let assump_27 := assump_3 assump_71
    apply False.elim assump_27


variable (p6 p5 p1 p0 p3 p7 : Prop)
theorem file76_28204 : ((((((p6 → True) → (p6 ∨ p3)) → False) → (((p1 → False) ∧ (p3 → True)) ∨ ((p6 → False) ∨ (True ∨ True)))) ∧ ((((p1 → p5) → (p0 ∨ p3)) → False) ∧ (((True ∨ p1) ∨ (p3 ∧ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : ((True ∨ p1) ∨ (p3 ∧ p7)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p2 p0 p7 p5 p4 p1 : Prop)
theorem file76_28782 : (((((p2 → False) → False) → ((p5 ∧ True) ∨ (p0 → p0))) → False) → ((((p0 ∨ p1) ∧ (False → p7)) → False) → (((True ∧ p4) ∨ (p0 ∨ p5)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      have assump_57 : (((p2 → False) → False) → ((p5 ∧ True) ∨ (p0 → p0))) := by
        intro assump_17
        apply Or.inr
        intro assump_20
        exact assump_20
      let assump_16 := assump_1 assump_57
      apply False.elim assump_16
  case inr assump_5 =>
    cases assump_5
    case inl assump_26 =>
      have assump_58 : (((p2 → False) → False) → ((p5 ∧ True) ∨ (p0 → p0))) := by
        intro assump_35
        apply Or.inr
        intro assump_38
        exact assump_38
      let assump_34 := assump_1 assump_58
      apply False.elim assump_34
    case inr assump_27 =>
      have assump_59 : (((p2 → False) → False) → ((p5 ∧ True) ∨ (p0 → p0))) := by
        intro assump_51
        apply Or.inl
        apply And.intro
        exact assump_27
        apply True.intro
      let assump_50 := assump_1 assump_59
      apply False.elim assump_50


variable (p4 p2 p7 p3 p5 p1 p6 : Prop)
theorem file76_30010 : (((((p5 → False) ∨ (p3 → p7)) ∧ ((p1 ∨ p1) ∧ (p1 → False))) → False) ∨ ((((False → False) ∨ (p6 → p7)) → False) ∧ (((p4 ∨ p2) → False) → False))) := by
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
          have assump_50 : p1 := by
            exact assump_10
          let assump_16 := assump_9 assump_50
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_51 : p1 := by
            exact assump_11
          let assump_24 := assump_9 assump_51
          apply False.elim assump_24
    case inr assump_5 =>
      cases assump_3
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          have assump_52 : p1 := by
            exact assump_32
          let assump_38 := assump_31 assump_52
          apply False.elim assump_38
        case inr assump_33 =>
          have assump_53 : p1 := by
            exact assump_33
          let assump_46 := assump_31 assump_53
          apply False.elim assump_46


variable (p3 p1 p7 p6 p4 p0 p5 p2 : Prop)
theorem file76_31257 : (((((p5 → False) ∨ (p1 ∧ p3)) → ((p4 ∨ p6) ∨ (p6 → p6))) → (((p3 → p2) → False) → ((p6 ∧ True) → (p0 → p6)))) → ((((p7 → p3) → (p5 → False)) → ((p2 → False) → False)) → (((p1 ∧ p1) ∧ (p2 ∧ p7)) ∨ ((p5 ∨ True) ∧ (p2 → p2))))) := by
  intro assump_1
  intro assump_2
  apply Or.inr
  apply And.intro
  apply Or.inr
  apply True.intro
  intro assump_7
  exact assump_7


variable (p3 p1 p2 p4 p6 p7 p5 : Prop)
theorem file76_31686 : (((((True → False) ∧ (p6 → False)) ∧ ((p6 → False) ∨ (p1 ∧ p5))) → (((p2 → False) → (p1 → False)) → False)) ∧ ((((p3 ∨ p6) → (p6 ∨ False)) ∧ ((p1 ∧ False) ∧ (False → p7))) → (((False ∨ p4) ∧ (p2 ∨ p4)) → False))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        have assump_76 : True := by
          apply True.intro
        let assump_19 := assump_7 assump_76
        apply False.elim assump_19
      case inr assump_14 =>
        cases assump_14
        case intro assump_23 assump_24 =>
          have assump_77 : True := by
            apply True.intro
          let assump_32 := assump_7 assump_77
          apply False.elim assump_32
  intro assump_36
  intro assump_37
  cases assump_37
  case intro assump_38 assump_39 =>
    cases assump_38
    case inl assump_40 =>
      apply False.elim assump_40
    case inr assump_41 =>
      cases assump_39
      case inl assump_46 =>
        cases assump_36
        case intro assump_50 assump_51 =>
          cases assump_51
          case intro assump_54 assump_55 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              apply False.elim assump_57
      case inr assump_47 =>
        cases assump_36
        case intro assump_64 assump_65 =>
          cases assump_65
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              apply False.elim assump_71


variable (p1 p0 p4 p3 p5 p2 p6 p7 : Prop)
theorem file76_33339 : (((((p7 → p6) → False) ∧ ((p0 → False) ∨ (False → False))) → (((p4 → p0) ∨ (p2 → False)) ∧ ((False ∨ p4) → (p0 → False)))) → ((((p6 → True) ∨ (p6 ∧ p7)) ∨ ((p1 ∨ p0) → (p0 ∨ p7))) ∨ (((p3 ∨ p5) → False) → ((p0 ∧ p6) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p6 p7 p4 p0 p3 : Prop)
theorem file76_33728 : ((((((p4 ∨ p4) ∧ (True → False)) → False) → False) ∧ ((((p6 → False) → (True ∨ p0)) ∧ ((p3 ∧ p7) ∧ (p7 → False))) ∧ (((True → False) → False) → ((p4 ∧ p0) → (False → True))))) → False) := by
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
            have assump_37 : p7 := by
              exact assump_15
            let assump_33 := assump_13 assump_37
            apply False.elim assump_33


variable (p4 p0 p7 p5 p1 p6 p3 p2 : Prop)
theorem file76_34458 : (((((p5 → False) → (p0 → False)) → ((False ∨ True) ∨ (p4 → False))) ∨ (((p7 ∨ p6) ∨ (True → p2)) ∧ ((p6 ∨ p4) → False))) → ((((p4 → False) ∧ (p0 ∨ p7)) → ((p6 ∧ False) → (p6 ∧ p4))) ∨ (((p4 ∧ p1) → (p6 ∧ p0)) ∧ ((True ∨ p3) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
    cases assump_7
    case intro assump_14 assump_15 =>
      apply False.elim assump_15
  case inr assump_3 =>
    cases assump_3
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_22
        case inl assump_24 =>
          apply Or.inl
          intro assump_30
          intro assump_31
          apply And.intro
          cases assump_31
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
          cases assump_31
          case intro assump_38 assump_39 =>
            apply False.elim assump_39
        case inr assump_25 =>
          apply Or.inl
          intro assump_48
          intro assump_49
          apply And.intro
          cases assump_49
          case intro assump_50 assump_51 =>
            apply False.elim assump_51
          cases assump_49
          case intro assump_56 assump_57 =>
            apply False.elim assump_57
      case inr assump_23 =>
        apply Or.inl
        intro assump_66
        intro assump_67
        apply And.intro
        cases assump_67
        case intro assump_68 assump_69 =>
          apply False.elim assump_69
        cases assump_67
        case intro assump_74 assump_75 =>
          apply False.elim assump_75


variable (p4 p2 p0 p5 p7 p1 p6 : Prop)
theorem file76_36251 : (((((True → p6) ∨ (p4 ∨ p0)) ∧ ((p1 → False) → (p7 ∧ p2))) ∧ (((p5 ∨ True) → False) ∧ ((False → False) → (p4 → False)))) → ((((True ∧ p5) ∧ (p1 → False)) ∧ ((p7 → p2) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_18
              case intro assump_27 assump_28 =>
                have assump_81 : (p5 ∨ True) := by
                  apply Or.inl
                  exact assump_8
                let assump_38 := assump_27 assump_81
                apply False.elim assump_38
            case inr assump_22 =>
              cases assump_22
              case inl assump_42 =>
                cases assump_18
                case intro assump_48 assump_49 =>
                  have assump_82 : (False → False) := by
                    intro assump_55
                    apply False.elim assump_55
                  let assump_54 := assump_49 assump_82
                  have assump_83 : p4 := by
                    exact assump_42
                  let assump_58 := assump_54 assump_83
                  apply False.elim assump_58
              case inr assump_43 =>
                cases assump_18
                case intro assump_66 assump_67 =>
                  have assump_84 : (p5 ∨ True) := by
                    apply Or.inl
                    exact assump_8
                  let assump_77 := assump_66 assump_84
                  apply False.elim assump_77


variable (p0 p4 p1 p3 p6 p7 p2 : Prop)
theorem file76_38088 : (((((False → p4) ∨ (p2 ∨ p0)) ∧ ((p0 ∧ False) → (False ∧ False))) ∨ (((p7 ∧ p3) → False) ∨ ((p7 → False) → (p2 ∧ True)))) ∨ ((((p6 ∧ False) ∨ (p0 ∨ p7)) → ((p0 ∨ p3) → False)) ∨ (((p1 ∧ False) → False) → ((p4 ∨ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  apply False.elim assump_1
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    apply False.elim assump_12


variable (p6 p5 p0 p7 : Prop)
theorem file76_38685 : ((((((True ∧ p6) → (p0 ∨ p7)) → False) → (((p6 ∧ p5) ∨ (False → False)) ∧ ((p5 ∧ p0) → (p6 → p5)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((True ∧ p6) → (p0 ∨ p7)) → False) → (((p6 ∧ p5) ∨ (False → False)) ∧ ((p5 ∧ p0) → (p6 → p5)))) := by
    intro assump_5
    apply And.intro
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
    intro assump_11
    intro assump_12
    cases assump_11
    case intro assump_15 assump_16 =>
      exact assump_15
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p0 p6 p7 p1 p4 p5 p3 p2 : Prop)
theorem file76_39305 : ((((((p5 ∧ p2) → False) ∨ ((p3 ∨ p4) ∨ (p6 ∨ p6))) ∧ (((p6 ∨ False) ∧ (p4 ∧ False)) ∧ ((p0 → False) ∨ (p3 → False)))) ∧ ((((p4 → False) → (p4 → True)) → ((p1 → False) ∨ (p7 ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              cases assump_13
              case intro assump_18 assump_19 =>
                apply False.elim assump_19
            case inr assump_15 =>
              apply False.elim assump_15
      case inr assump_7 =>
        cases assump_7
        case inl assump_26 =>
          cases assump_26
          case inl assump_28 =>
            cases assump_5
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_34
                case inl assump_36 =>
                  cases assump_35
                  case intro assump_40 assump_41 =>
                    apply False.elim assump_41
                case inr assump_37 =>
                  apply False.elim assump_37
          case inr assump_29 =>
            cases assump_5
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_52
                case inl assump_54 =>
                  cases assump_53
                  case intro assump_58 assump_59 =>
                    apply False.elim assump_59
                case inr assump_55 =>
                  apply False.elim assump_55
        case inr assump_27 =>
          cases assump_27
          case inl assump_66 =>
            cases assump_5
            case intro assump_70 assump_71 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                cases assump_72
                case inl assump_74 =>
                  cases assump_73
                  case intro assump_78 assump_79 =>
                    apply False.elim assump_79
                case inr assump_75 =>
                  apply False.elim assump_75
          case inr assump_67 =>
            cases assump_5
            case intro assump_88 assump_89 =>
              cases assump_88
              case intro assump_90 assump_91 =>
                cases assump_90
                case inl assump_92 =>
                  cases assump_91
                  case intro assump_96 assump_97 =>
                    apply False.elim assump_97
                case inr assump_93 =>
                  apply False.elim assump_93


variable (p0 p3 p4 p1 p5 p2 p6 p7 : Prop)
theorem file76_42179 : (((((p2 ∨ p6) ∨ (p2 → p5)) → False) → (((p6 ∨ p7) → (p1 → p5)) → ((p4 ∧ p0) → False))) ∨ ((((p1 → False) → (p0 ∧ p7)) → ((p6 ∧ p3) → (p6 → p7))) ∨ (((p0 ∧ p4) → False) → False))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_30 : ((p2 ∨ p6) ∨ (p2 → p5)) := by
      apply Or.inr
      intro assump_19
      have assump_31 : ((p2 ∨ p6) ∨ (p2 → p5)) := by
        apply Or.inl
        apply Or.inl
        exact assump_19
      let assump_23 := assump_5 assump_31
      apply False.elim assump_23
    let assump_18 := assump_5 assump_30
    apply False.elim assump_18


variable (p6 p2 p5 p3 p7 p4 : Prop)
theorem file76_42898 : (((((p6 → False) → False) ∨ ((p5 → False) → False)) ∧ (((p2 → False) ∧ (True → False)) ∧ ((p6 ∨ p6) → False))) → ((((True ∧ p4) → False) ∧ ((p4 → False) ∨ (p3 → False))) ∨ (((p4 ∧ False) → (p7 ∨ False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          apply And.intro
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            have assump_74 : True := by
              apply True.intro
            let assump_27 := assump_11 assump_74
            apply False.elim assump_27
          apply Or.inl
          intro assump_31
          have assump_75 : True := by
            apply True.intro
          let assump_36 := assump_11 assump_75
          apply False.elim assump_36
    case inr assump_5 =>
      cases assump_3
      case intro assump_42 assump_43 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          apply Or.inl
          apply And.intro
          intro assump_52
          cases assump_52
          case intro assump_53 assump_54 =>
            have assump_76 : True := by
              apply True.intro
            let assump_61 := assump_45 assump_76
            apply False.elim assump_61
          apply Or.inl
          intro assump_65
          have assump_77 : True := by
            apply True.intro
          let assump_70 := assump_45 assump_77
          apply False.elim assump_70


variable (p4 p7 p1 p2 p0 : Prop)
theorem file76_44571 : ((((((True ∧ p1) → False) → ((False → False) ∨ (p0 ∧ True))) → False) ∧ ((((p4 → p2) ∨ (p4 → p2)) ∧ ((p0 ∧ p7) ∨ (p2 → False))) ∧ (((False → p1) ∨ (True → p7)) → False))) → False) := by
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
              have assump_72 : ((False → p1) ∨ (True → p7)) := by
                apply Or.inl
                intro assump_25
                apply False.elim assump_25
              let assump_24 := assump_7 assump_72
              apply False.elim assump_24
          case inr assump_15 =>
            have assump_73 : ((False → p1) ∨ (True → p7)) := by
              apply Or.inl
              intro assump_36
              apply False.elim assump_36
            let assump_35 := assump_7 assump_73
            apply False.elim assump_35
        case inr assump_11 =>
          cases assump_9
          case inl assump_44 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              have assump_74 : ((False → p1) ∨ (True → p7)) := by
                apply Or.inl
                intro assump_55
                apply False.elim assump_55
              let assump_54 := assump_7 assump_74
              apply False.elim assump_54
          case inr assump_45 =>
            have assump_75 : ((False → p1) ∨ (True → p7)) := by
              apply Or.inl
              intro assump_66
              apply False.elim assump_66
            let assump_65 := assump_7 assump_75
            apply False.elim assump_65


variable (p7 p3 p1 p2 p4 p0 : Prop)
theorem file76_46428 : ((((((True ∨ p7) → False) ∧ ((p2 → False) ∨ (p1 ∧ True))) → (((p3 → p0) ∧ (p2 ∧ p2)) ∨ ((p3 ∧ p0) ∧ (p7 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_51 : ((((True ∨ p7) → False) ∧ ((p2 → False) ∨ (p1 ∧ True))) → (((p3 → p0) ∧ (p2 ∧ p2)) ∨ ((p3 ∧ p0) ∧ (p7 ∧ p4)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_52 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_24 := assump_6 assump_52
        apply False.elim assump_24
      case inr assump_11 =>
        cases assump_11
        case intro assump_28 assump_29 =>
          have assump_53 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_44 := assump_6 assump_53
          apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p3 p6 p0 p1 : Prop)
theorem file76_47408 : (((((False → False) → (p3 → p0)) → ((False → False) ∨ (p3 → False))) → False) → ((((False ∧ p1) → False) ∨ ((p6 → False) → False)) → (((p6 ∨ p0) → False) ∨ ((p3 → p3) ∨ (p1 → False))))) := by
  intro assump_12
  intro assump_13
  cases assump_13
  case inl assump_14 =>
    apply Or.inl
    intro assump_20
    cases assump_20
    case inl assump_21 =>
      have assump_82 : (((False → False) → (p3 → p0)) → ((False → False) ∨ (p3 → False))) := by
        intro assump_27
        apply Or.inl
        intro assump_30
        apply False.elim assump_30
      let assump_26 := assump_12 assump_82
      apply False.elim assump_26
    case inr assump_22 =>
      have assump_83 : (((False → False) → (p3 → p0)) → ((False → False) ∨ (p3 → False))) := by
        intro assump_40
        apply Or.inl
        intro assump_43
        apply False.elim assump_43
      let assump_39 := assump_12 assump_83
      apply False.elim assump_39
  case inr assump_15 =>
    apply Or.inl
    intro assump_53
    cases assump_53
    case inl assump_54 =>
      have assump_84 : (((False → False) → (p3 → p0)) → ((False → False) ∨ (p3 → False))) := by
        intro assump_60
        apply Or.inl
        intro assump_63
        apply False.elim assump_63
      let assump_59 := assump_12 assump_84
      apply False.elim assump_59
    case inr assump_55 =>
      have assump_85 : (((False → False) → (p3 → p0)) → ((False → False) ∨ (p3 → False))) := by
        intro assump_73
        apply Or.inl
        intro assump_76
        apply False.elim assump_76
      let assump_72 := assump_12 assump_85
      apply False.elim assump_72


variable (p5 p1 p6 p0 : Prop)
theorem file76_49078 : ((((((False ∧ p5) → False) → False) → False) → ((((p0 → False) → False) → ((p6 → True) → (True ∨ p1))) → False)) → False) := by
  intro assump_1
  have assump_27 : ((((False ∧ p5) → False) → False) → False) := by
    intro assump_5
    have assump_28 : ((False ∧ p5) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_28
    apply False.elim assump_8
  let assump_4 := assump_1 assump_27
  have assump_29 : (((p0 → False) → False) → ((p6 → True) → (True ∨ p1))) := by
    intro assump_18
    intro assump_19
    apply Or.inl
    apply True.intro
  let assump_17 := assump_4 assump_29
  apply False.elim assump_17


variable (p2 p7 p6 p0 : Prop)
theorem file76_49862 : (((((True ∧ p7) ∧ (p0 → False)) → False) → False) → ((((False → p6) ∨ (p0 ∨ p0)) ∨ ((p7 → False) → False)) ∨ (((p2 ∨ p2) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p0 p4 p5 p3 p7 p6 p2 : Prop)
theorem file76_50179 : (((((p4 ∧ p7) → False) → ((False ∧ p0) → False)) ∨ (((p6 → False) ∧ (p5 ∧ p7)) ∧ ((p3 ∧ p2) → (p0 ∨ p3)))) ∨ ((((p4 → False) → False) → False) ∧ (((p2 ∨ p7) ∧ (p5 ∨ p2)) ∧ ((p0 ∨ p2) ∨ (p3 ∧ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p5 p2 p6 p0 p7 p1 p3 p4 : Prop)
theorem file76_50595 : (((((True ∧ p6) → (p4 → False)) → ((p1 ∨ False) ∨ (p7 → p5))) ∨ (((p1 → False) → False) ∨ ((p2 ∧ p5) ∨ (p2 → False)))) → ((((True ∧ p6) → (False → p1)) ∨ ((False → False) → (p1 → p0))) ∨ (((False ∨ p4) ∨ (p6 → False)) ∧ ((p6 → p3) ∧ (p6 ∨ p7))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case inl assump_10 =>
      apply Or.inl
      apply Or.inl
      intro assump_14
      intro assump_15
      apply False.elim assump_15
    case inr assump_11 =>
      cases assump_11
      case inl assump_18 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply Or.inl
          intro assump_26
          intro assump_27
          apply False.elim assump_27
      case inr assump_19 =>
        apply Or.inl
        apply Or.inl
        intro assump_32
        intro assump_33
        apply False.elim assump_33


variable (p6 p7 p2 p5 p1 p3 p0 : Prop)
theorem file76_51683 : (((((p0 ∧ p0) ∨ (False → p3)) → ((p5 ∨ p7) ∨ (p2 ∧ p3))) → False) → ((((p5 ∧ p7) ∧ (p1 ∨ p1)) → False) ∨ (((p0 → False) → (p2 → p6)) ∨ ((p3 ∧ True) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        have assump_55 : (((p0 ∧ p0) ∨ (False → p3)) → ((p5 ∨ p7) ∨ (p2 ∧ p3))) := by
          intro assump_21
          cases assump_21
          case inl assump_22 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              apply Or.inl
              apply Or.inl
              exact assump_7
          case inr assump_23 =>
            apply Or.inl
            apply Or.inl
            exact assump_7
        let assump_20 := assump_1 assump_55
        apply False.elim assump_20
      case inr assump_14 =>
        have assump_56 : (((p0 ∧ p0) ∨ (False → p3)) → ((p5 ∨ p7) ∨ (p2 ∧ p3))) := by
          intro assump_41
          cases assump_41
          case inl assump_42 =>
            cases assump_42
            case intro assump_44 assump_45 =>
              apply Or.inl
              apply Or.inl
              exact assump_7
          case inr assump_43 =>
            apply Or.inl
            apply Or.inl
            exact assump_7
        let assump_40 := assump_1 assump_56
        apply False.elim assump_40


variable (p0 p7 p3 p1 p2 p5 p4 p6 : Prop)
theorem file76_53177 : (((((p3 ∧ False) → False) ∨ ((p6 → False) ∧ (p5 → False))) ∨ (((p4 → False) ∨ (p7 → p6)) ∨ ((p1 → p1) → (False → p7)))) ∨ ((((True ∧ p2) ∨ (p7 → p1)) → False) ∨ (((False ∧ p2) → False) ∧ ((p6 → p4) ∨ (p0 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    apply False.elim assump_17


variable (p7 p2 p5 p0 p4 p6 : Prop)
theorem file76_53605 : ((((((False ∨ False) ∨ (True ∨ p0)) → False) → (((p7 ∨ p7) ∨ (p2 → False)) ∨ ((p5 ∧ p5) ∨ (p6 → False)))) → ((((p4 ∨ p6) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_1
  have assump_41 : ((((False ∨ False) ∨ (True ∨ p0)) → False) → (((p7 ∨ p7) ∨ (p2 → False)) ∨ ((p5 ∧ p5) ∨ (p6 → False)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    intro assump_8
    have assump_42 : ((False ∨ False) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_12 := assump_5 assump_42
    apply False.elim assump_12
  let assump_4 := assump_1 assump_41
  have assump_43 : (((p4 ∨ p6) ∧ (True → False)) → False) := by
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        have assump_44 : True := by
          apply True.intro
        let assump_26 := assump_19 assump_44
        apply False.elim assump_26
      case inr assump_21 =>
        have assump_45 : True := by
          apply True.intro
        let assump_34 := assump_19 assump_45
        apply False.elim assump_34
  let assump_16 := assump_4 assump_43
  apply False.elim assump_16


variable (p0 p5 p6 p2 p3 p4 : Prop)
theorem file76_54857 : (((((p5 ∨ p6) ∧ (p4 ∧ p2)) ∨ ((p6 → False) → (p2 ∧ p4))) → False) → ((((True ∨ p3) ∨ (p2 → True)) → ((False ∧ p0) → (p5 → False))) ∨ (((False ∨ p6) ∨ (p2 → False)) ∧ ((p4 ∨ p4) ∨ (p2 ∨ p4))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    apply False.elim assump_9


variable (p0 p4 p5 p3 p7 : Prop)
theorem file76_55278 : (((((p5 ∧ p5) → False) → False) → (((p7 ∧ p3) → (True ∧ p3)) ∨ ((p4 → False) → False))) ∨ ((((p3 ∧ True) ∨ (True → p0)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  apply True.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    exact assump_6


variable (p0 : Prop)
theorem file76_55639 : (((((True ∨ p0) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p0) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p0) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p4 p1 p7 p5 : Prop)
theorem file76_56062 : ((((((True → False) → False) → ((p5 ∨ p5) → False)) → (((p1 → p2) → False) → ((p4 ∧ p7) ∨ (p5 → False)))) → False) → False) := by
  intro assump_40
  have assump_69 : ((((True → False) → False) → ((p5 ∨ p5) → False)) → (((p1 → p2) → False) → ((p4 ∧ p7) ∨ (p5 → False)))) := by
    intro assump_44
    intro assump_45
    apply Or.inr
    intro assump_50
    have assump_70 : ((True → False) → False) := by
      intro assump_55
      have assump_71 : True := by
        apply True.intro
      let assump_58 := assump_55 assump_71
      apply False.elim assump_58
    let assump_54 := assump_44 assump_70
    have assump_72 : (p5 ∨ p5) := by
      apply Or.inl
      exact assump_50
    let assump_62 := assump_54 assump_72
    apply False.elim assump_62
  let assump_43 := assump_40 assump_69
  apply False.elim assump_43


variable (p4 p7 : Prop)
theorem file76_56932 : ((((((p4 → False) → False) ∧ ((p7 → False) ∧ (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p4 → False) → False) ∧ ((p7 → False) ∧ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_11 assump_24
        apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p2 p6 p5 p7 p1 p0 p3 : Prop)
theorem file76_57547 : (((((True ∨ p7) → False) ∨ ((False ∨ p7) → (p7 → p1))) → (((p6 ∨ p6) → (True ∨ p3)) ∨ ((p0 ∨ p4) ∧ (p5 → p6)))) ∨ ((((p2 → p4) → False) ∧ ((p2 ∧ p2) → (True → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
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
    apply Or.inl
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      apply Or.inl
      apply True.intro
    case inr assump_17 =>
      apply Or.inl
      apply True.intro


variable (p2 p3 p7 p5 p4 p1 p6 p0 : Prop)
theorem file76_58274 : (((((p6 ∧ p2) ∧ (p0 → p0)) ∧ ((p2 ∨ p1) ∧ (p3 ∨ p5))) → (((False ∨ False) → False) ∨ ((False → False) ∧ (True ∧ p6)))) → ((((p7 → p4) ∧ (p3 ∧ p0)) ∧ ((p1 → p1) → False)) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        have assump_31 : (p1 → p1) := by
          intro assump_25
          exact assump_25
        let assump_24 := assump_8 assump_31
        apply False.elim assump_24


variable (p6 p1 p7 p0 p3 : Prop)
theorem file76_58892 : ((((((p6 → False) → False) → ((False → False) ∨ (p0 ∧ p7))) ∨ (((p3 ∧ p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p6 → False) → False) → ((False → False) ∨ (p0 ∧ p7))) ∨ (((p3 ∧ p1) → False) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p2 p4 p3 p7 p5 p0 : Prop)
theorem file76_59372 : ((((((p2 → p2) ∨ (p5 ∧ p6)) → ((True ∧ p5) → False)) → False) ∧ ((((True → p7) ∨ (p0 → False)) ∨ ((True → p7) ∧ (p4 ∨ p5))) ∧ (((True → p4) ∧ (p7 → False)) ∧ ((True → False) ∧ (p2 ∧ p3))))) → False) := by
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
            case intro assump_16 assump_17 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  have assump_122 : True := by
                    apply True.intro
                  let assump_34 := assump_22 assump_122
                  apply False.elim assump_34
        case inr assump_11 =>
          cases assump_7
          case intro assump_40 assump_41 =>
            cases assump_40
            case intro assump_42 assump_43 =>
              cases assump_41
              case intro assump_48 assump_49 =>
                cases assump_49
                case intro assump_52 assump_53 =>
                  have assump_123 : True := by
                    apply True.intro
                  let assump_60 := assump_48 assump_123
                  apply False.elim assump_60
      case inr assump_9 =>
        cases assump_9
        case intro assump_64 assump_65 =>
          cases assump_65
          case inl assump_68 =>
            cases assump_7
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                cases assump_73
                case intro assump_80 assump_81 =>
                  cases assump_81
                  case intro assump_84 assump_85 =>
                    have assump_124 : True := by
                      apply True.intro
                    let assump_92 := assump_80 assump_124
                    apply False.elim assump_92
          case inr assump_69 =>
            cases assump_7
            case intro assump_98 assump_99 =>
              cases assump_98
              case intro assump_100 assump_101 =>
                cases assump_99
                case intro assump_106 assump_107 =>
                  cases assump_107
                  case intro assump_110 assump_111 =>
                    have assump_125 : True := by
                      apply True.intro
                    let assump_118 := assump_106 assump_125
                    apply False.elim assump_118


variable (p0 p4 p2 p3 p5 p7 p6 : Prop)
theorem file76_62086 : (((((p7 → False) → False) ∨ ((p6 ∧ p0) → (True ∧ p0))) ∨ (((p3 ∧ p2) ∨ (p5 ∧ p3)) ∨ ((p0 → False) → False))) → ((((p2 → False) → (p7 ∨ p4)) ∧ ((False ∧ p0) ∨ (p3 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_8 =>
      cases assump_8
      case intro assump_13 assump_14 =>
        apply False.elim assump_14


variable (p2 p1 p5 p4 : Prop)
theorem file76_62673 : (((((False ∧ p5) ∧ (p1 ∧ p5)) → ((p4 ∧ p2) ∧ (p5 ∧ p2))) → False) → False) := by
  intro assump_1
  have assump_33 : (((False ∧ p5) ∧ (p1 ∧ p5)) → ((p4 ∧ p2) ∧ (p5 ∧ p2))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    apply And.intro
    cases assump_5
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_20
    cases assump_5
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p6 p7 p1 p0 p5 : Prop)
theorem file76_63662 : ((((((p6 ∨ p7) ∧ (p5 ∨ p7)) ∧ ((p0 → False) ∧ (p0 ∧ p1))) → False) → False) → False) := by
  intro assump_1
  have assump_95 : ((((p6 ∨ p7) ∧ (p5 ∨ p7)) ∧ ((p0 → False) ∧ (p0 ∧ p1))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                have assump_96 : p0 := by
                  exact assump_22
                let assump_30 := assump_18 assump_96
                apply False.elim assump_30
          case inr assump_15 =>
            cases assump_7
            case intro assump_36 assump_37 =>
              cases assump_37
              case intro assump_40 assump_41 =>
                have assump_97 : p0 := by
                  exact assump_40
                let assump_48 := assump_36 assump_97
                apply False.elim assump_48
        case inr assump_11 =>
          cases assump_9
          case inl assump_54 =>
            cases assump_7
            case intro assump_58 assump_59 =>
              cases assump_59
              case intro assump_62 assump_63 =>
                have assump_98 : p0 := by
                  exact assump_62
                let assump_70 := assump_58 assump_98
                apply False.elim assump_70
          case inr assump_55 =>
            cases assump_7
            case intro assump_76 assump_77 =>
              cases assump_77
              case intro assump_80 assump_81 =>
                have assump_99 : p0 := by
                  exact assump_80
                let assump_88 := assump_76 assump_99
                apply False.elim assump_88
  let assump_4 := assump_1 assump_95
  apply False.elim assump_4


variable (p3 p5 p6 p7 p0 p4 p1 : Prop)
theorem file76_65674 : (((((p5 → p5) → (p4 ∨ True)) ∨ ((p1 ∧ p4) ∨ (p6 → p0))) → False) → ((((p3 ∧ True) → (p6 ∨ p7)) → ((p3 → False) → (p0 → False))) → (((p6 ∨ p5) → (p4 ∨ p3)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_17 : (((p5 → p5) → (p4 ∨ True)) ∨ ((p1 ∧ p4) ∨ (p6 → p0))) := by
    apply Or.inl
    intro assump_11
    apply Or.inr
    apply True.intro
  let assump_10 := assump_1 assump_17
  apply False.elim assump_10


variable (p3 p7 p4 : Prop)
theorem file76_66169 : ((((((p7 ∨ True) ∧ (True ∨ p7)) ∨ ((p4 → True) ∧ (p3 ∧ True))) ∧ (((False → False) ∧ (True → False)) → False)) → False) → False) := by
  intro assump_26
  have assump_44 : ((((p7 ∨ True) ∧ (True ∨ p7)) ∨ ((p4 → True) ∧ (p3 ∧ True))) ∧ (((False → False) ∧ (True → False)) → False)) := by
    apply And.intro
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply True.intro
    apply Or.inl
    apply True.intro
    intro assump_30
    cases assump_30
    case intro assump_31 assump_32 =>
      have assump_45 : True := by
        apply True.intro
      let assump_37 := assump_32 assump_45
      apply False.elim assump_37
  let assump_29 := assump_26 assump_44
  apply False.elim assump_29


variable (p7 p6 p5 p2 p1 p0 : Prop)
theorem file76_66930 : ((((((p0 → False) ∨ (p7 ∨ p5)) ∨ ((p1 → False) ∨ (p6 → p1))) → (((p2 ∨ p5) ∧ (True ∨ True)) ∨ ((False → False) ∨ (p1 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p0 → False) ∨ (p7 ∨ p5)) ∨ ((p1 → False) ∨ (p6 → p1))) → (((p2 ∨ p5) ∧ (True ∨ True)) ∨ ((False → False) ∨ (p1 ∨ p2)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        apply Or.inl
        intro assump_12
        apply False.elim assump_12
      case inr assump_9 =>
        cases assump_9
        case inl assump_15 =>
          apply Or.inr
          apply Or.inl
          intro assump_19
          apply False.elim assump_19
        case inr assump_16 =>
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_16
          apply Or.inl
          apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_24 =>
        apply Or.inr
        apply Or.inl
        intro assump_28
        apply False.elim assump_28
      case inr assump_25 =>
        apply Or.inr
        apply Or.inl
        intro assump_33
        apply False.elim assump_33
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p7 p5 p1 p3 p0 p6 p4 : Prop)
theorem file76_68257 : (((((p3 → p3) → (False ∨ p6)) ∨ ((p7 → False) → False)) ∨ (((False ∨ p6) → (p5 ∧ p6)) → False)) → ((((p1 → True) ∧ (p6 → p6)) → ((False ∧ p4) → (True → p5))) ∨ (((False → False) → (p0 → False)) → ((True → True) ∧ (True ∨ True))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    case inr assump_5 =>
      apply Or.inl
      intro assump_19
      intro assump_20
      intro assump_21
      cases assump_20
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  case inr assump_3 =>
    apply Or.inl
    intro assump_30
    intro assump_31
    intro assump_32
    cases assump_31
    case intro assump_35 assump_36 =>
      apply False.elim assump_35


variable (p3 p6 p1 p4 p2 p5 : Prop)
theorem file76_69232 : ((((((p1 ∧ p5) ∧ (p3 ∧ False)) → False) ∨ (((p2 → p4) → False) → ((p4 → True) → False))) → ((((True ∨ p5) ∧ (p4 → p4)) ∨ ((p4 → False) ∧ (p6 → False))) → False)) → False) := by
  intro assump_1
  have assump_27 : ((((p1 ∧ p5) ∧ (p3 ∧ False)) → False) ∨ (((p2 → p4) → False) → ((p4 → True) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_27
  have assump_28 : (((True ∨ p5) ∧ (p4 → p4)) ∨ ((p4 → False) ∧ (p6 → False))) := by
    apply Or.inl
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_21
    exact assump_21
  let assump_20 := assump_4 assump_28
  apply False.elim assump_20


variable (p0 p4 p3 p7 p6 p5 : Prop)
theorem file76_70154 : ((((((p7 → False) ∨ (p5 ∧ p4)) ∨ ((False ∨ p5) ∨ (p4 → False))) ∧ (((True → False) → (p6 → False)) ∧ ((p0 → False) ∧ (p7 ∧ p4)))) ∧ ((((p6 → False) ∨ (p0 → False)) ∧ ((False → False) → False)) ∧ (((p5 ∧ True) → False) ∨ ((p6 ∨ p3) → False)))) → False) := by
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
            cases assump_13
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_27
                      case inl assump_36 =>
                        have assump_300 : (False → False) := by
                          intro assump_42
                          apply False.elim assump_42
                        let assump_41 := assump_29 assump_300
                        apply False.elim assump_41
                      case inr assump_37 =>
                        have assump_301 : (False → False) := by
                          intro assump_52
                          apply False.elim assump_52
                        let assump_51 := assump_29 assump_301
                        apply False.elim assump_51
                    case inr assump_31 =>
                      cases assump_27
                      case inl assump_62 =>
                        have assump_302 : (False → False) := by
                          intro assump_68
                          apply False.elim assump_68
                        let assump_67 := assump_29 assump_302
                        apply False.elim assump_67
                      case inr assump_63 =>
                        have assump_303 : (False → False) := by
                          intro assump_78
                          apply False.elim assump_78
                        let assump_77 := assump_29 assump_303
                        apply False.elim assump_77
        case inr assump_9 =>
          cases assump_9
          case intro assump_84 assump_85 =>
            cases assump_5
            case intro assump_90 assump_91 =>
              cases assump_91
              case intro assump_94 assump_95 =>
                cases assump_95
                case intro assump_98 assump_99 =>
                  cases assump_3
                  case intro assump_104 assump_105 =>
                    cases assump_104
                    case intro assump_106 assump_107 =>
                      cases assump_106
                      case inl assump_108 =>
                        cases assump_105
                        case inl assump_114 =>
                          have assump_304 : (p5 ∧ True) := by
                            apply And.intro
                            exact assump_84
                            apply True.intro
                          let assump_118 := assump_114 assump_304
                          apply False.elim assump_118
                        case inr assump_115 =>
                          have assump_305 : (False → False) := by
                            intro assump_126
                            apply False.elim assump_126
                          let assump_125 := assump_107 assump_305
                          apply False.elim assump_125
                      case inr assump_109 =>
                        cases assump_105
                        case inl assump_136 =>
                          have assump_306 : (p5 ∧ True) := by
                            apply And.intro
                            exact assump_84
                            apply True.intro
                          let assump_140 := assump_136 assump_306
                          apply False.elim assump_140
                        case inr assump_137 =>
                          have assump_307 : (False → False) := by
                            intro assump_148
                            apply False.elim assump_148
                          let assump_147 := assump_107 assump_307
                          apply False.elim assump_147
      case inr assump_7 =>
        cases assump_7
        case inl assump_154 =>
          cases assump_154
          case inl assump_156 =>
            apply False.elim assump_156
          case inr assump_157 =>
            cases assump_5
            case intro assump_162 assump_163 =>
              cases assump_163
              case intro assump_166 assump_167 =>
                cases assump_167
                case intro assump_170 assump_171 =>
                  cases assump_3
                  case intro assump_176 assump_177 =>
                    cases assump_176
                    case intro assump_178 assump_179 =>
                      cases assump_178
                      case inl assump_180 =>
                        cases assump_177
                        case inl assump_186 =>
                          have assump_308 : (p5 ∧ True) := by
                            apply And.intro
                            exact assump_157
                            apply True.intro
                          let assump_190 := assump_186 assump_308
                          apply False.elim assump_190
                        case inr assump_187 =>
                          have assump_309 : (False → False) := by
                            intro assump_198
                            apply False.elim assump_198
                          let assump_197 := assump_179 assump_309
                          apply False.elim assump_197
                      case inr assump_181 =>
                        cases assump_177
                        case inl assump_208 =>
                          have assump_310 : (p5 ∧ True) := by
                            apply And.intro
                            exact assump_157
                            apply True.intro
                          let assump_212 := assump_208 assump_310
                          apply False.elim assump_212
                        case inr assump_209 =>
                          have assump_311 : (False → False) := by
                            intro assump_220
                            apply False.elim assump_220
                          let assump_219 := assump_179 assump_311
                          apply False.elim assump_219
        case inr assump_155 =>
          cases assump_5
          case intro assump_228 assump_229 =>
            cases assump_229
            case intro assump_232 assump_233 =>
              cases assump_233
              case intro assump_236 assump_237 =>
                cases assump_3
                case intro assump_242 assump_243 =>
                  cases assump_242
                  case intro assump_244 assump_245 =>
                    cases assump_244
                    case inl assump_246 =>
                      cases assump_243
                      case inl assump_252 =>
                        have assump_312 : (False → False) := by
                          intro assump_258
                          apply False.elim assump_258
                        let assump_257 := assump_245 assump_312
                        apply False.elim assump_257
                      case inr assump_253 =>
                        have assump_313 : (False → False) := by
                          intro assump_268
                          apply False.elim assump_268
                        let assump_267 := assump_245 assump_313
                        apply False.elim assump_267
                    case inr assump_247 =>
                      cases assump_243
                      case inl assump_278 =>
                        have assump_314 : (False → False) := by
                          intro assump_284
                          apply False.elim assump_284
                        let assump_283 := assump_245 assump_314
                        apply False.elim assump_283
                      case inr assump_279 =>
                        have assump_315 : (False → False) := by
                          intro assump_294
                          apply False.elim assump_294
                        let assump_293 := assump_245 assump_315
                        apply False.elim assump_293


variable (p7 p3 p0 p1 p5 p6 p2 : Prop)
theorem file76_78821 : (((((True ∨ p6) → False) → False) → False) → ((((p0 ∨ p7) → (True ∧ p5)) → ((True → p6) ∨ (False → p2))) ∨ (((p3 ∨ p0) → (p1 ∧ p5)) → ((p7 → p2) ∨ (False ∨ p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  have assump_22 : (((True ∨ p6) → False) → False) := by
    intro assump_12
    have assump_23 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_15 := assump_12 assump_23
    apply False.elim assump_15
  let assump_11 := assump_1 assump_22
  apply False.elim assump_11


variable (p4 p0 p6 p5 p7 p1 : Prop)
theorem file76_79429 : (((((p0 ∧ p1) → (p5 → False)) ∧ ((True → False) ∧ (p6 → False))) → (((p1 → p6) ∨ (p1 → False)) → False)) ∨ ((((p7 → p7) ∧ (p1 ∧ p4)) → ((False → p0) → (p1 ∨ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_39 : True := by
          apply True.intro
        let assump_18 := assump_11 assump_39
        apply False.elim assump_18
  case inr assump_4 =>
    cases assump_1
    case intro assump_24 assump_25 =>
      cases assump_25
      case intro assump_28 assump_29 =>
        have assump_40 : True := by
          apply True.intro
        let assump_35 := assump_28 assump_40
        apply False.elim assump_35


variable (p0 p3 p5 p4 p7 p2 p6 p1 : Prop)
theorem file76_80307 : (((((p4 ∧ p5) ∧ (p2 → p7)) ∧ ((False → p3) → False)) → (((p7 → p4) ∨ (p4 ∧ True)) → ((p7 ∨ p6) ∨ (p4 ∧ p6)))) → ((((p7 → p6) → False) ∧ ((p0 → p1) → False)) → (((p2 → False) ∨ (False → False)) → ((p7 ∨ p6) ∨ (p4 → p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      apply Or.inr
      intro assump_16
      exact assump_16
  case inr assump_5 =>
    cases assump_2
    case intro assump_21 assump_22 =>
      apply Or.inr
      intro assump_29
      exact assump_29


variable (p1 p5 p6 p0 p4 p2 p7 p3 : Prop)
theorem file76_80953 : (((((p1 ∨ p1) → False) → ((p4 ∧ p1) ∨ (p1 → p0))) → False) → ((((p7 → p1) ∨ (p5 ∨ p0)) ∨ ((False ∧ p4) ∧ (p4 ∧ p6))) ∨ (((p1 ∨ p3) → (p5 → False)) ∧ ((p0 ∨ p4) → (p3 ∨ p2))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_23 : (((p1 ∨ p1) → False) → ((p4 ∧ p1) ∨ (p1 → p0))) := by
    intro assump_9
    apply Or.inr
    intro assump_12
    have assump_24 : (p1 ∨ p1) := by
      apply Or.inl
      exact assump_12
    let assump_16 := assump_9 assump_24
    apply False.elim assump_16
  let assump_8 := assump_1 assump_23
  apply False.elim assump_8


variable (p1 p2 p0 p6 p3 p5 p4 p7 : Prop)
theorem file76_81623 : (((((p2 → False) ∨ (p7 ∨ p1)) → ((p0 ∧ True) ∨ (p4 → False))) ∨ (((p4 ∧ p1) → False) ∨ ((p0 ∧ True) ∧ (p0 → False)))) → ((((p6 → True) → False) → False) ∨ (((p3 → p2) → (p5 ∨ p6)) ∧ ((p2 → p1) ∧ (p1 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_44 : (p6 → True) := by
      intro assump_10
      apply True.intro
    let assump_9 := assump_6 assump_44
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case inl assump_14 =>
      apply Or.inl
      intro assump_18
      have assump_45 : (p6 → True) := by
        intro assump_22
        apply True.intro
      let assump_21 := assump_18 assump_45
      apply False.elim assump_21
    case inr assump_15 =>
      cases assump_15
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply Or.inl
          intro assump_36
          have assump_46 : (p6 → True) := by
            intro assump_40
            apply True.intro
          let assump_39 := assump_36 assump_46
          apply False.elim assump_39


variable (p3 p7 p2 : Prop)
theorem file76_82802 : ((((((True ∨ p2) → (p3 → False)) ∧ ((True ∨ True) → False)) → False) → ((((p7 ∧ p3) ∧ (False → False)) → ((p2 → p3) ∨ (True → p3))) → False)) → False) := by
  intro assump_1
  have assump_34 : ((((True ∨ p2) → (p3 → False)) ∧ ((True ∨ True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_35 : (True ∨ True) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_35
      apply False.elim assump_12
  let assump_4 := assump_1 assump_34
  have assump_36 : (((p7 ∧ p3) ∧ (False → False)) → ((p2 → p3) ∨ (True → p3))) := by
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply Or.inl
        intro assump_28
        exact assump_21
  let assump_16 := assump_4 assump_36
  apply False.elim assump_16


variable (p5 p7 p6 p1 p4 p3 : Prop)
theorem file76_83764 : ((((((True → False) ∨ (p7 ∨ p5)) ∧ ((p7 ∧ p3) → (True ∧ p1))) ∨ (((p3 → True) ∧ (p4 → False)) → False)) ∧ ((((p6 → True) ∨ (p5 ∨ p7)) → ((p1 ∨ p5) ∨ (p1 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          have assump_146 : (((p6 → True) ∨ (p5 ∨ p7)) → ((p1 ∨ p5) ∨ (p1 → p7))) := by
            intro assump_17
            cases assump_17
            case inl assump_18 =>
              apply Or.inr
              intro assump_22
              have assump_147 : (((p6 → True) ∨ (p5 ∨ p7)) → ((p1 ∨ p5) ∨ (p1 → p7))) := by
                intro assump_28
                cases assump_28
                case inl assump_29 =>
                  apply Or.inl
                  apply Or.inl
                  exact assump_22
                case inr assump_30 =>
                  cases assump_30
                  case inl assump_33 =>
                    apply Or.inl
                    apply Or.inl
                    exact assump_22
                  case inr assump_34 =>
                    apply Or.inl
                    apply Or.inl
                    exact assump_22
              let assump_27 := assump_3 assump_147
              apply False.elim assump_27
            case inr assump_19 =>
              cases assump_19
              case inl assump_42 =>
                apply Or.inl
                apply Or.inr
                exact assump_42
              case inr assump_43 =>
                apply Or.inr
                intro assump_48
                exact assump_43
          let assump_16 := assump_3 assump_146
          apply False.elim assump_16
        case inr assump_9 =>
          cases assump_9
          case inl assump_54 =>
            have assump_148 : (((p6 → True) ∨ (p5 ∨ p7)) → ((p1 ∨ p5) ∨ (p1 → p7))) := by
              intro assump_63
              cases assump_63
              case inl assump_64 =>
                apply Or.inr
                intro assump_68
                exact assump_54
              case inr assump_65 =>
                cases assump_65
                case inl assump_71 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_71
                case inr assump_72 =>
                  apply Or.inr
                  intro assump_77
                  exact assump_72
            let assump_62 := assump_3 assump_148
            apply False.elim assump_62
          case inr assump_55 =>
            have assump_149 : (((p6 → True) ∨ (p5 ∨ p7)) → ((p1 ∨ p5) ∨ (p1 → p7))) := by
              intro assump_90
              cases assump_90
              case inl assump_91 =>
                apply Or.inl
                apply Or.inr
                exact assump_55
              case inr assump_92 =>
                cases assump_92
                case inl assump_95 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_95
                case inr assump_96 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_55
            let assump_89 := assump_3 assump_149
            apply False.elim assump_89
    case inr assump_5 =>
      have assump_150 : (((p6 → True) ∨ (p5 ∨ p7)) → ((p1 ∨ p5) ∨ (p1 → p7))) := by
        intro assump_109
        cases assump_109
        case inl assump_110 =>
          apply Or.inr
          intro assump_114
          have assump_151 : (((p6 → True) ∨ (p5 ∨ p7)) → ((p1 ∨ p5) ∨ (p1 → p7))) := by
            intro assump_120
            cases assump_120
            case inl assump_121 =>
              apply Or.inl
              apply Or.inl
              exact assump_114
            case inr assump_122 =>
              cases assump_122
              case inl assump_125 =>
                apply Or.inl
                apply Or.inl
                exact assump_114
              case inr assump_126 =>
                apply Or.inl
                apply Or.inl
                exact assump_114
          let assump_119 := assump_3 assump_151
          apply False.elim assump_119
        case inr assump_111 =>
          cases assump_111
          case inl assump_134 =>
            apply Or.inl
            apply Or.inr
            exact assump_134
          case inr assump_135 =>
            apply Or.inr
            intro assump_140
            exact assump_135
      let assump_108 := assump_3 assump_150
      apply False.elim assump_108


variable (p7 p0 p3 p2 p1 : Prop)
theorem file76_88408 : ((((((p0 → p7) ∧ (p0 → p7)) ∧ ((p2 ∨ p1) → (p7 → p7))) → False) ∧ ((((p7 ∧ True) ∨ (False → False)) ∨ ((p7 ∨ p3) ∧ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p7 ∧ True) ∨ (False → False)) ∨ ((p7 ∨ p3) ∧ (p3 → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p4 p5 p6 p1 p0 p2 p7 : Prop)
theorem file76_88947 : (((((p7 ∧ p0) ∧ (False ∨ p3)) ∧ ((p7 → False) → False)) → (((False → False) → (p7 → False)) ∨ ((p5 → True) ∨ (p0 → p7)))) → ((((p2 ∧ p6) ∧ (p6 → False)) ∧ ((False → False) → False)) → (((p3 ∧ p5) ∧ (p4 → False)) → ((p1 ∨ True) → (p6 → False))))) := by
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
      case intro assump_14 assump_15 =>
        cases assump_2
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              have assump_82 : (False → False) := by
                intro assump_40
                apply False.elim assump_40
              let assump_39 := assump_23 assump_82
              apply False.elim assump_39
  case inr assump_9 =>
    cases assump_3
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        cases assump_2
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            cases assump_60
            case intro assump_62 assump_63 =>
              have assump_83 : (False → False) := by
                intro assump_76
                apply False.elim assump_76
              let assump_75 := assump_59 assump_83
              apply False.elim assump_75


variable (p7 p4 p1 p3 p5 p2 : Prop)
theorem file76_90503 : (((((p4 ∨ p2) → False) → ((p1 ∧ p7) → False)) ∨ (((True ∧ True) → (False → p4)) ∧ ((p2 ∧ p3) → (False ∧ p3)))) → ((((p7 → False) → False) ∨ ((False ∨ p3) → False)) → (((p3 → False) → (False → False)) ∨ ((p4 → False) ∧ (p2 → p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inl
      intro assump_11
      intro assump_12
      apply False.elim assump_12
    case inr assump_8 =>
      cases assump_8
      case intro assump_15 assump_16 =>
        apply Or.inl
        intro assump_21
        intro assump_22
        apply False.elim assump_22
  case inr assump_4 =>
    cases assump_1
    case inl assump_27 =>
      apply Or.inl
      intro assump_31
      intro assump_32
      apply False.elim assump_32
    case inr assump_28 =>
      cases assump_28
      case intro assump_35 assump_36 =>
        apply Or.inl
        intro assump_41
        intro assump_42
        apply False.elim assump_42


variable (p1 p5 p4 p2 p7 p0 p3 : Prop)
theorem file76_91564 : ((((((p2 ∨ p5) ∨ (False ∨ False)) ∨ ((False ∨ p1) ∨ (p1 → p3))) → False) ∨ ((((p7 ∧ p0) ∨ (p3 ∨ p5)) ∧ ((p7 → p0) → False)) ∧ (((p4 ∨ p1) ∧ (p7 → False)) ∧ ((p3 → p0) ∧ (p7 → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_206 : (((p2 ∨ p5) ∨ (False ∨ False)) ∨ ((False ∨ p1) ∨ (p1 → p3))) := by
      apply Or.inr
      apply Or.inr
      intro assump_7
      have assump_207 : (((p2 ∨ p5) ∨ (False ∨ False)) ∨ ((False ∨ p1) ∨ (p1 → p3))) := by
        apply Or.inr
        apply Or.inl
        apply Or.inr
        exact assump_7
      let assump_11 := assump_2 assump_207
      apply False.elim assump_11
    let assump_6 := assump_2 assump_206
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            cases assump_19
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_34
                case inl assump_36 =>
                  cases assump_33
                  case intro assump_42 assump_43 =>
                    have assump_208 : p7 := by
                      exact assump_24
                    let assump_51 := assump_35 assump_208
                    apply False.elim assump_51
                case inr assump_37 =>
                  cases assump_33
                  case intro assump_59 assump_60 =>
                    have assump_209 : p7 := by
                      exact assump_24
                    let assump_68 := assump_35 assump_209
                    apply False.elim assump_68
        case inr assump_23 =>
          cases assump_23
          case inl assump_72 =>
            cases assump_19
            case intro assump_78 assump_79 =>
              cases assump_78
              case intro assump_80 assump_81 =>
                cases assump_80
                case inl assump_82 =>
                  cases assump_79
                  case intro assump_88 assump_89 =>
                    have assump_210 : (p7 → p0) := by
                      intro assump_100
                      have assump_211 : p3 := by
                        exact assump_72
                      let assump_106 := assump_88 assump_211
                      exact assump_106
                    let assump_99 := assump_21 assump_210
                    apply False.elim assump_99
                case inr assump_83 =>
                  cases assump_79
                  case intro assump_115 assump_116 =>
                    have assump_212 : (p7 → p0) := by
                      intro assump_127
                      have assump_213 : p3 := by
                        exact assump_72
                      let assump_133 := assump_115 assump_213
                      exact assump_133
                    let assump_126 := assump_21 assump_212
                    apply False.elim assump_126
          case inr assump_73 =>
            cases assump_19
            case intro assump_142 assump_143 =>
              cases assump_142
              case intro assump_144 assump_145 =>
                cases assump_144
                case inl assump_146 =>
                  cases assump_143
                  case intro assump_152 assump_153 =>
                    have assump_214 : (p7 → p0) := by
                      intro assump_163
                      have assump_215 : p7 := by
                        exact assump_163
                      let assump_170 := assump_145 assump_215
                      apply False.elim assump_170
                    let assump_162 := assump_21 assump_214
                    apply False.elim assump_162
                case inr assump_147 =>
                  cases assump_143
                  case intro assump_181 assump_182 =>
                    have assump_216 : (p7 → p0) := by
                      intro assump_192
                      have assump_217 : p7 := by
                        exact assump_192
                      let assump_199 := assump_145 assump_217
                      apply False.elim assump_199
                    let assump_191 := assump_21 assump_216
                    apply False.elim assump_191


variable (p5 p2 p0 p4 p7 p1 p3 : Prop)
theorem file76_96012 : (((((True ∧ p0) ∧ (False → p5)) ∨ ((p3 ∧ p5) → False)) ∧ (((p7 ∨ p4) ∧ (p2 ∧ p7)) ∨ ((False → p1) → False))) → ((((p3 ∨ False) ∨ (p0 → False)) ∧ ((True → False) ∨ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_4
        case inl assump_11 =>
          cases assump_1
          case intro assump_15 assump_16 =>
            cases assump_15
            case inl assump_17 =>
              cases assump_17
              case intro assump_19 assump_20 =>
                cases assump_19
                case intro assump_21 assump_22 =>
                  cases assump_16
                  case inl assump_29 =>
                    cases assump_29
                    case intro assump_31 assump_32 =>
                      cases assump_31
                      case inl assump_33 =>
                        cases assump_32
                        case intro assump_37 assump_38 =>
                          have assump_475 : True := by
                            apply True.intro
                          let assump_48 := assump_11 assump_475
                          apply False.elim assump_48
                      case inr assump_34 =>
                        cases assump_32
                        case intro assump_54 assump_55 =>
                          have assump_476 : True := by
                            apply True.intro
                          let assump_65 := assump_11 assump_476
                          apply False.elim assump_65
                  case inr assump_30 =>
                    have assump_477 : (False → p1) := by
                      intro assump_72
                      apply False.elim assump_72
                    let assump_71 := assump_30 assump_477
                    apply False.elim assump_71
            case inr assump_18 =>
              cases assump_16
              case inl assump_80 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  cases assump_82
                  case inl assump_84 =>
                    cases assump_83
                    case intro assump_88 assump_89 =>
                      have assump_478 : True := by
                        apply True.intro
                      let assump_98 := assump_11 assump_478
                      apply False.elim assump_98
                  case inr assump_85 =>
                    cases assump_83
                    case intro assump_104 assump_105 =>
                      have assump_479 : True := by
                        apply True.intro
                      let assump_114 := assump_11 assump_479
                      apply False.elim assump_114
              case inr assump_81 =>
                have assump_480 : (False → p1) := by
                  intro assump_121
                  apply False.elim assump_121
                let assump_120 := assump_81 assump_480
                apply False.elim assump_120
        case inr assump_12 =>
          cases assump_1
          case intro assump_129 assump_130 =>
            cases assump_129
            case inl assump_131 =>
              cases assump_131
              case intro assump_133 assump_134 =>
                cases assump_133
                case intro assump_135 assump_136 =>
                  cases assump_130
                  case inl assump_143 =>
                    cases assump_143
                    case intro assump_145 assump_146 =>
                      cases assump_145
                      case inl assump_147 =>
                        cases assump_146
                        case intro assump_151 assump_152 =>
                          have assump_481 : True := by
                            apply True.intro
                          let assump_162 := assump_12 assump_481
                          apply False.elim assump_162
                      case inr assump_148 =>
                        cases assump_146
                        case intro assump_168 assump_169 =>
                          have assump_482 : True := by
                            apply True.intro
                          let assump_179 := assump_12 assump_482
                          apply False.elim assump_179
                  case inr assump_144 =>
                    have assump_483 : (False → p1) := by
                      intro assump_186
                      apply False.elim assump_186
                    let assump_185 := assump_144 assump_483
                    apply False.elim assump_185
            case inr assump_132 =>
              cases assump_130
              case inl assump_194 =>
                cases assump_194
                case intro assump_196 assump_197 =>
                  cases assump_196
                  case inl assump_198 =>
                    cases assump_197
                    case intro assump_202 assump_203 =>
                      have assump_484 : True := by
                        apply True.intro
                      let assump_212 := assump_12 assump_484
                      apply False.elim assump_212
                  case inr assump_199 =>
                    cases assump_197
                    case intro assump_218 assump_219 =>
                      have assump_485 : True := by
                        apply True.intro
                      let assump_228 := assump_12 assump_485
                      apply False.elim assump_228
              case inr assump_195 =>
                have assump_486 : (False → p1) := by
                  intro assump_235
                  apply False.elim assump_235
                let assump_234 := assump_195 assump_486
                apply False.elim assump_234
      case inr assump_8 =>
        apply False.elim assump_8
    case inr assump_6 =>
      cases assump_4
      case inl assump_245 =>
        cases assump_1
        case intro assump_249 assump_250 =>
          cases assump_249
          case inl assump_251 =>
            cases assump_251
            case intro assump_253 assump_254 =>
              cases assump_253
              case intro assump_255 assump_256 =>
                cases assump_250
                case inl assump_263 =>
                  cases assump_263
                  case intro assump_265 assump_266 =>
                    cases assump_265
                    case inl assump_267 =>
                      cases assump_266
                      case intro assump_271 assump_272 =>
                        have assump_487 : True := by
                          apply True.intro
                        let assump_282 := assump_245 assump_487
                        apply False.elim assump_282
                    case inr assump_268 =>
                      cases assump_266
                      case intro assump_288 assump_289 =>
                        have assump_488 : True := by
                          apply True.intro
                        let assump_299 := assump_245 assump_488
                        apply False.elim assump_299
                case inr assump_264 =>
                  have assump_489 : (False → p1) := by
                    intro assump_306
                    apply False.elim assump_306
                  let assump_305 := assump_264 assump_489
                  apply False.elim assump_305
          case inr assump_252 =>
            cases assump_250
            case inl assump_314 =>
              cases assump_314
              case intro assump_316 assump_317 =>
                cases assump_316
                case inl assump_318 =>
                  cases assump_317
                  case intro assump_322 assump_323 =>
                    have assump_490 : True := by
                      apply True.intro
                    let assump_332 := assump_245 assump_490
                    apply False.elim assump_332
                case inr assump_319 =>
                  cases assump_317
                  case intro assump_338 assump_339 =>
                    have assump_491 : True := by
                      apply True.intro
                    let assump_348 := assump_245 assump_491
                    apply False.elim assump_348
            case inr assump_315 =>
              have assump_492 : (False → p1) := by
                intro assump_355
                apply False.elim assump_355
              let assump_354 := assump_315 assump_492
              apply False.elim assump_354
      case inr assump_246 =>
        cases assump_1
        case intro assump_363 assump_364 =>
          cases assump_363
          case inl assump_365 =>
            cases assump_365
            case intro assump_367 assump_368 =>
              cases assump_367
              case intro assump_369 assump_370 =>
                cases assump_364
                case inl assump_377 =>
                  cases assump_377
                  case intro assump_379 assump_380 =>
                    cases assump_379
                    case inl assump_381 =>
                      cases assump_380
                      case intro assump_385 assump_386 =>
                        have assump_493 : True := by
                          apply True.intro
                        let assump_396 := assump_246 assump_493
                        apply False.elim assump_396
                    case inr assump_382 =>
                      cases assump_380
                      case intro assump_402 assump_403 =>
                        have assump_494 : True := by
                          apply True.intro
                        let assump_413 := assump_246 assump_494
                        apply False.elim assump_413
                case inr assump_378 =>
                  have assump_495 : (False → p1) := by
                    intro assump_420
                    apply False.elim assump_420
                  let assump_419 := assump_378 assump_495
                  apply False.elim assump_419
          case inr assump_366 =>
            cases assump_364
            case inl assump_428 =>
              cases assump_428
              case intro assump_430 assump_431 =>
                cases assump_430
                case inl assump_432 =>
                  cases assump_431
                  case intro assump_436 assump_437 =>
                    have assump_496 : True := by
                      apply True.intro
                    let assump_446 := assump_246 assump_496
                    apply False.elim assump_446
                case inr assump_433 =>
                  cases assump_431
                  case intro assump_452 assump_453 =>
                    have assump_497 : True := by
                      apply True.intro
                    let assump_462 := assump_246 assump_497
                    apply False.elim assump_462
            case inr assump_429 =>
              have assump_498 : (False → p1) := by
                intro assump_469
                apply False.elim assump_469
              let assump_468 := assump_429 assump_498
              apply False.elim assump_468


variable (p3 p7 p1 p6 p4 p0 p5 : Prop)
theorem file76_107225 : ((((((p3 → False) ∧ (p7 → p6)) → ((p4 ∨ False) → (p0 → False))) → (((p1 ∧ p4) ∨ (False → False)) ∨ ((p5 → p6) ∧ (True → False)))) → False) → False) := by
  intro assump_32
  have assump_45 : ((((p3 → False) ∧ (p7 → p6)) → ((p4 ∨ False) → (p0 → False))) → (((p1 ∧ p4) ∨ (False → False)) ∨ ((p5 → p6) ∧ (True → False)))) := by
    intro assump_36
    apply Or.inl
    apply Or.inr
    intro assump_39
    apply False.elim assump_39
  let assump_35 := assump_32 assump_45
  apply False.elim assump_35


variable (p2 p3 p0 p6 p7 p4 : Prop)
theorem file76_107783 : (((((True ∨ True) ∨ (p0 ∨ p7)) → False) → (((p4 → True) → (p3 → p3)) ∧ ((p7 → False) → False))) ∨ ((((p2 → p7) → False) ∨ ((p2 ∨ p7) ∨ (p2 → False))) ∧ (((p6 → False) ∧ (False ∧ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  exact assump_3
  intro assump_10
  have assump_19 : ((True ∨ True) ∨ (p0 ∨ p7)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_15 := assump_1 assump_19
  apply False.elim assump_15


variable (p3 p1 p4 : Prop)
theorem file76_108328 : (((((p1 ∧ p3) ∨ (p1 → False)) → ((p4 ∨ True) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p1 ∧ p3) ∨ (p1 → False)) → ((p4 ∨ True) → (False → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p2 p1 p3 p7 : Prop)
theorem file76_108728 : ((((((p7 → False) ∧ (False ∧ False)) → ((False ∧ True) → False)) ∨ (((True ∨ p1) ∧ (p2 → p3)) → False)) → False) → False) := by
  intro assump_41
  have assump_54 : ((((p7 → False) ∧ (False ∧ False)) → ((False ∧ True) → False)) ∨ (((True ∨ p1) ∧ (p2 → p3)) → False)) := by
    apply Or.inl
    intro assump_45
    intro assump_46
    cases assump_46
    case intro assump_47 assump_48 =>
      apply False.elim assump_47
  let assump_44 := assump_41 assump_54
  apply False.elim assump_44


variable (p6 p4 p0 p5 p3 p7 : Prop)
theorem file76_109277 : ((((((p0 ∨ p7) → False) → False) ∧ (((p5 → False) → False) ∧ ((p3 ∧ False) ∧ (True → False)))) ∧ ((((True ∨ p4) ∨ (p7 → False)) ∨ ((p7 → p7) → (p7 → p6))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply False.elim assump_19


variable (p3 p2 p1 p5 p4 p0 p7 : Prop)
theorem file76_109879 : (((((p7 → True) → (True → False)) ∨ ((p3 → p4) ∨ (True ∨ p5))) → (((False ∨ p7) → (p0 ∨ True)) ∨ ((p5 → False) → (p4 → p1)))) ∨ ((((p1 ∨ True) → (True ∧ p5)) → False) → (((p2 → False) → False) ∧ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_32
  cases assump_32
  case inl assump_33 =>
    apply Or.inl
    intro assump_37
    cases assump_37
    case inl assump_38 =>
      apply False.elim assump_38
    case inr assump_39 =>
      apply Or.inr
      apply True.intro
  case inr assump_34 =>
    cases assump_34
    case inl assump_44 =>
      apply Or.inl
      intro assump_48
      cases assump_48
      case inl assump_49 =>
        apply False.elim assump_49
      case inr assump_50 =>
        apply Or.inr
        apply True.intro
    case inr assump_45 =>
      cases assump_45
      case inl assump_55 =>
        apply Or.inl
        intro assump_59
        cases assump_59
        case inl assump_60 =>
          apply False.elim assump_60
        case inr assump_61 =>
          apply Or.inr
          apply True.intro
      case inr assump_56 =>
        apply Or.inl
        intro assump_68
        cases assump_68
        case inl assump_69 =>
          apply False.elim assump_69
        case inr assump_70 =>
          apply Or.inr
          apply True.intro


variable (p7 p0 p6 p3 p4 p2 p1 : Prop)
theorem file76_111234 : (((((True → False) → False) → False) → False) ∧ ((((p1 ∧ p2) ∧ (p1 ∨ p4)) ∧ ((p7 → False) → (p0 ∧ p3))) ∨ (((p1 ∨ True) ∨ (True → False)) ∧ ((False ∧ True) → (p6 ∧ p0))))) := by
  apply And.intro
  intro assump_36
  have assump_59 : ((True → False) → False) := by
    intro assump_40
    have assump_60 : True := by
      apply True.intro
    let assump_43 := assump_40 assump_60
    apply False.elim assump_43
  let assump_39 := assump_36 assump_59
  apply False.elim assump_39
  apply Or.inr
  apply And.intro
  apply Or.inl
  apply Or.inr
  apply True.intro
  intro assump_50
  apply And.intro
  cases assump_50
  case intro assump_51 assump_52 =>
    apply False.elim assump_51
  cases assump_50
  case intro assump_55 assump_56 =>
    apply False.elim assump_55


variable (p6 p3 p5 p2 p0 : Prop)
theorem file76_112058 : ((((((p2 → False) → (p3 → True)) → ((p5 → False) → (p3 ∨ True))) ∨ (((p0 ∨ p3) → False) → ((p0 ∨ p5) → (p6 → p2)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → False) → (p3 → True)) → ((p5 → False) → (p3 ∨ True))) ∨ (((p0 ∨ p3) → False) → ((p0 ∨ p5) → (p6 → p2)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p1 p2 p0 p4 p5 p3 : Prop)
theorem file76_112575 : (((((p5 ∨ p1) → False) → ((p0 → False) ∨ (p1 → p3))) → (((p3 → False) → False) → False)) → ((((p6 ∧ p4) ∧ (p6 → p2)) → ((p0 → True) ∧ (p2 → True))) ∨ (((True ∧ p5) → (False → p0)) ∨ ((p6 → False) → (p3 ∧ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  apply True.intro
  intro assump_6
  apply True.intro


variable (p0 p6 p5 p2 p1 p4 : Prop)
theorem file76_112992 : (((((True ∨ p2) → (p5 ∨ True)) ∨ ((p2 → True) → False)) → (((p2 → False) ∧ (p2 → False)) → False)) → ((((p5 ∧ False) → (p0 → True)) ∨ ((p2 ∨ True) → (p1 ∨ p1))) ∨ (((p6 → False) ∨ (p1 → False)) ∨ ((p5 → p4) ∨ (False → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p7 p4 p6 p2 p5 p0 p3 p1 : Prop)
theorem file76_113393 : (((((p1 ∨ p4) ∨ (p4 → p2)) → False) ∧ (((p0 ∧ p3) ∧ (p5 → p5)) → ((p3 → False) ∨ (p6 → p3)))) → ((((p6 ∧ True) ∨ (p7 → p5)) → False) ∨ (((p5 → False) → False) → False))) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    apply Or.inl
    intro assump_18
    cases assump_18
    case inl assump_19 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        have assump_61 : ((p1 ∨ p4) ∨ (p4 → p2)) := by
          apply Or.inr
          intro assump_30
          have assump_62 : ((p1 ∨ p4) ∨ (p4 → p2)) := by
            apply Or.inl
            apply Or.inr
            exact assump_30
          let assump_36 := assump_12 assump_62
          apply False.elim assump_36
        let assump_29 := assump_12 assump_61
        apply False.elim assump_29
    case inr assump_20 =>
      have assump_63 : ((p1 ∨ p4) ∨ (p4 → p2)) := by
        apply Or.inr
        intro assump_48
        have assump_64 : ((p1 ∨ p4) ∨ (p4 → p2)) := by
          apply Or.inl
          apply Or.inr
          exact assump_48
        let assump_54 := assump_12 assump_64
        apply False.elim assump_54
      let assump_47 := assump_12 assump_63
      apply False.elim assump_47


variable (p7 p4 p1 p3 p2 p5 p6 : Prop)
theorem file76_114659 : ((((((p3 → p6) ∨ (p5 → p4)) ∧ ((p2 ∨ p3) → (p5 ∧ p7))) → False) ∧ ((((p5 → p1) → False) → ((True ∨ p2) ∨ (True ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p5 → p1) → False) → ((True ∨ p2) ∨ (True ∧ p5))) := by
      intro assump_9
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p4 p2 p3 p7 p6 p1 p5 p0 : Prop)
theorem file76_115167 : (((((False ∧ p7) → (p6 ∨ True)) ∨ ((p4 ∨ True) ∨ (p4 → p1))) → False) → ((((p0 ∧ p5) ∧ (p6 ∨ p3)) → False) → (((p2 → p4) → False) ∧ ((p6 ∧ p5) → (p6 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  have assump_42 : (((False ∧ p7) → (p6 ∨ True)) ∨ ((p4 ∨ True) ∨ (p4 → p1))) := by
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_10 := assump_1 assump_42
  apply False.elim assump_10
  intro assump_19
  intro assump_20
  cases assump_19
  case intro assump_23 assump_24 =>
    have assump_43 : (((False ∧ p7) → (p6 ∨ True)) ∨ ((p4 ∨ True) ∨ (p4 → p1))) := by
      apply Or.inl
      intro assump_34
      cases assump_34
      case intro assump_35 assump_36 =>
        apply False.elim assump_35
    let assump_33 := assump_1 assump_43
    apply False.elim assump_33


variable (p6 p0 p4 p3 p2 : Prop)
theorem file76_116125 : (((((False → p4) ∨ (p6 → p2)) ∨ ((p2 ∧ p0) ∧ (True ∨ p4))) → (((p3 ∨ p6) → (p3 → True)) ∨ ((p2 → False) → False))) ∨ ((((p4 ∨ p6) ∨ (True → p2)) ∨ ((p0 ∨ p4) ∧ (p6 → False))) ∨ (((p4 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      intro assump_9
      apply True.intro
    case inr assump_5 =>
      apply Or.inl
      intro assump_12
      intro assump_13
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_15
        case inl assump_22 =>
          apply Or.inl
          intro assump_26
          intro assump_27
          apply True.intro
        case inr assump_23 =>
          apply Or.inl
          intro assump_30
          intro assump_31
          apply True.intro


variable (p4 p6 p2 p7 p1 p3 p5 : Prop)
theorem file76_117147 : (((((p6 → False) ∧ (True ∨ p3)) ∧ ((p3 ∨ p3) ∨ (p3 → False))) → (((p6 ∧ p5) ∧ (p3 → False)) → ((p2 ∨ p7) → (p4 ∨ p4)))) ∨ ((((p1 ∧ p7) → False) ∧ ((p7 → False) ∨ (p7 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_1
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_21
            case inl assump_24 =>
              cases assump_19
              case inl assump_28 =>
                cases assump_28
                case inl assump_30 =>
                  have assump_156 : p6 := by
                    exact assump_10
                  let assump_35 := assump_20 assump_156
                  apply False.elim assump_35
                case inr assump_31 =>
                  have assump_157 : p6 := by
                    exact assump_10
                  let assump_42 := assump_20 assump_157
                  apply False.elim assump_42
              case inr assump_29 =>
                have assump_158 : p6 := by
                  exact assump_10
                let assump_49 := assump_20 assump_158
                apply False.elim assump_49
            case inr assump_25 =>
              cases assump_19
              case inl assump_55 =>
                cases assump_55
                case inl assump_57 =>
                  have assump_159 : p6 := by
                    exact assump_10
                  let assump_63 := assump_20 assump_159
                  apply False.elim assump_63
                case inr assump_58 =>
                  have assump_160 : p6 := by
                    exact assump_10
                  let assump_71 := assump_20 assump_160
                  apply False.elim assump_71
              case inr assump_56 =>
                have assump_161 : p3 := by
                  exact assump_25
                let assump_77 := assump_56 assump_161
                apply False.elim assump_77
  case inr assump_5 =>
    cases assump_2
    case intro assump_83 assump_84 =>
      cases assump_83
      case intro assump_85 assump_86 =>
        cases assump_1
        case intro assump_93 assump_94 =>
          cases assump_93
          case intro assump_95 assump_96 =>
            cases assump_96
            case inl assump_99 =>
              cases assump_94
              case inl assump_103 =>
                cases assump_103
                case inl assump_105 =>
                  have assump_162 : p6 := by
                    exact assump_85
                  let assump_110 := assump_95 assump_162
                  apply False.elim assump_110
                case inr assump_106 =>
                  have assump_163 : p6 := by
                    exact assump_85
                  let assump_117 := assump_95 assump_163
                  apply False.elim assump_117
              case inr assump_104 =>
                have assump_164 : p6 := by
                  exact assump_85
                let assump_124 := assump_95 assump_164
                apply False.elim assump_124
            case inr assump_100 =>
              cases assump_94
              case inl assump_130 =>
                cases assump_130
                case inl assump_132 =>
                  have assump_165 : p6 := by
                    exact assump_85
                  let assump_138 := assump_95 assump_165
                  apply False.elim assump_138
                case inr assump_133 =>
                  have assump_166 : p6 := by
                    exact assump_85
                  let assump_146 := assump_95 assump_166
                  apply False.elim assump_146
              case inr assump_131 =>
                have assump_167 : p3 := by
                  exact assump_100
                let assump_152 := assump_131 assump_167
                apply False.elim assump_152


variable (p7 p3 p6 : Prop)
theorem file76_121234 : ((((((p6 → False) → False) → ((p6 → False) → (False → False))) ∨ (((p3 ∨ p7) ∨ (p3 → p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p6 → False) → False) → ((p6 → False) → (False → False))) ∨ (((p3 ∨ p7) ∨ (p3 → p6)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p0 p2 p7 p1 p3 p4 p6 : Prop)
theorem file76_121730 : (((((False ∧ p3) → (False → p2)) ∨ ((p2 → False) ∧ (p1 → False))) ∨ (((p0 ∨ False) → (p6 ∧ p4)) ∧ ((p3 → False) → (p4 ∧ p7)))) ∨ ((((p6 → False) ∧ (p7 → False)) → False) ∧ (((p4 → p7) → (p4 → False)) → ((p2 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p1 p2 p5 p6 p4 p7 p0 : Prop)
theorem file76_122134 : ((((((True ∧ False) → (p1 ∨ p5)) → False) → (((p2 → p4) → False) → False)) → ((((p6 ∧ p4) → False) → ((p4 ∨ p7) ∨ (p7 → p0))) → False)) → False) := by
  intro assump_1
  have assump_59 : ((((True ∧ False) → (p1 ∨ p5)) → False) → (((p2 → p4) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_60 : ((True ∧ False) → (p1 ∨ p5)) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_11 := assump_5 assump_60
    apply False.elim assump_11
  let assump_4 := assump_1 assump_59
  have assump_61 : (((p6 ∧ p4) → False) → ((p4 ∨ p7) ∨ (p7 → p0))) := by
    intro assump_23
    apply Or.inr
    intro assump_26
    have assump_62 : ((((True ∧ False) → (p1 ∨ p5)) → False) → (((p2 → p4) → False) → False)) := by
      intro assump_32
      intro assump_33
      have assump_63 : ((True ∧ False) → (p1 ∨ p5)) := by
        intro assump_39
        cases assump_39
        case intro assump_40 assump_41 =>
          apply False.elim assump_41
      let assump_38 := assump_32 assump_63
      apply False.elim assump_38
    let assump_31 := assump_1 assump_62
    have assump_64 : (((p6 ∧ p4) → False) → ((p4 ∨ p7) ∨ (p7 → p0))) := by
      intro assump_50
      apply Or.inl
      apply Or.inr
      exact assump_26
    let assump_49 := assump_31 assump_64
    apply False.elim assump_49
  let assump_22 := assump_4 assump_61
  apply False.elim assump_22


variable (p4 p6 p2 p0 p1 : Prop)
theorem file76_123649 : (((((p4 ∧ p1) → (p6 → p1)) ∨ ((p1 → False) → False)) ∧ (((p2 → p6) ∧ (p0 → False)) ∧ ((p1 → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_40 : (p1 → True) := by
            intro assump_19
            apply True.intro
          let assump_18 := assump_9 assump_40
          apply False.elim assump_18
    case inr assump_5 =>
      cases assump_3
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          have assump_41 : (p1 → True) := by
            intro assump_36
            apply True.intro
          let assump_35 := assump_26 assump_41
          apply False.elim assump_35


variable (p7 p1 p3 : Prop)
theorem file76_124583 : ((((((p1 → False) → (p7 → p7)) → ((p3 → False) ∧ (False ∨ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p1 → False) → (p7 → p7)) → ((p3 → False) ∧ (False ∨ p3))) → False) := by
    intro assump_5
    have assump_41 : ((p1 → False) → (p7 → p7)) := by
      intro assump_9
      intro assump_10
      exact assump_10
    let assump_8 := assump_5 assump_41
    let assump_15 := And.right assump_8
    cases assump_15
    case inl assump_18 =>
      apply False.elim assump_18
    case inr assump_19 =>
      have assump_42 : ((p1 → False) → (p7 → p7)) := by
        intro assump_26
        intro assump_27
        exact assump_27
      let assump_25 := assump_5 assump_42
      let assump_32 := And.left assump_25
      have assump_43 : p3 := by
        exact assump_19
      let assump_33 := assump_32 assump_43
      apply False.elim assump_33
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p5 p3 p0 p6 p4 p2 p7 p1 : Prop)
theorem file76_125590 : (((((p0 → False) ∧ (False → p6)) ∧ ((p0 ∨ p2) → False)) → (((p3 ∨ p1) ∧ (p0 ∧ p6)) → ((p5 → False) → (p7 ∨ p0)))) ∨ ((((True ∨ p5) ∨ (p6 → p7)) ∨ ((p2 ∧ p3) ∨ (p4 ∧ p4))) → (((p2 ∨ True) ∧ (False → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_1
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply Or.inr
            exact assump_12
    case inr assump_9 =>
      cases assump_7
      case intro assump_30 assump_31 =>
        cases assump_1
        case intro assump_36 assump_37 =>
          cases assump_36
          case intro assump_38 assump_39 =>
            apply Or.inr
            exact assump_30


variable (p1 p3 p0 p5 p4 p7 p6 : Prop)
theorem file76_126557 : (((((p1 → p6) ∧ (True → False)) ∧ ((p7 → True) → (False ∧ False))) → False) ∨ ((((p1 → False) → (p5 → False)) ∨ ((True → False) ∧ (p0 ∨ False))) ∨ (((p3 → p4) → (p1 ∨ p1)) → ((p4 ∨ False) → False)))) := by
  apply Or.inl
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      have assump_26 : (p7 → True) := by
        intro assump_21
        apply True.intro
      let assump_20 := assump_11 assump_26
      let assump_22 := And.left assump_20
      apply False.elim assump_22


variable (p4 p7 p1 p2 : Prop)
theorem file76_127168 : (((((p1 ∨ False) → (p4 ∧ p2)) → False) ∧ (((p4 → p1) ∨ (False ∧ False)) ∧ ((True ∨ p7) → (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_50 : ((p1 ∨ False) → (p4 ∧ p2)) := by
          intro assump_18
          apply And.intro
          cases assump_18
          case inl assump_19 =>
            have assump_51 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_24 := assump_7 assump_51
            have assump_52 : p1 := by
              exact assump_19
            let assump_25 := assump_24 assump_52
            apply False.elim assump_25
          case inr assump_20 =>
            apply False.elim assump_20
          cases assump_18
          case inl assump_31 =>
            have assump_53 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_36 := assump_7 assump_53
            have assump_54 : p1 := by
              exact assump_31
            let assump_37 := assump_36 assump_54
            apply False.elim assump_37
          case inr assump_32 =>
            apply False.elim assump_32
        let assump_17 := assump_2 assump_50
        apply False.elim assump_17
      case inr assump_9 =>
        cases assump_9
        case intro assump_46 assump_47 =>
          apply False.elim assump_46


variable (p2 p6 p1 p0 p4 : Prop)
theorem file76_128710 : ((((((True → False) ∧ (p4 → p2)) ∧ ((p6 ∧ p1) ∨ (p0 → True))) → (((p4 ∧ p6) → (False → p6)) → ((p6 → p4) → False))) → False) → False) := by
  intro assump_10
  have assump_55 : ((((True → False) ∧ (p4 → p2)) ∧ ((p6 ∧ p1) ∨ (p0 → True))) → (((p4 ∧ p6) → (False → p6)) → ((p6 → p4) → False))) := by
    intro assump_14
    intro assump_15
    intro assump_16
    cases assump_14
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_22
        case inl assump_29 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            have assump_56 : True := by
              apply True.intro
            let assump_40 := assump_23 assump_56
            apply False.elim assump_40
        case inr assump_30 =>
          have assump_57 : True := by
            apply True.intro
          let assump_48 := assump_23 assump_57
          apply False.elim assump_48
  let assump_13 := assump_10 assump_55
  apply False.elim assump_13


variable (p1 p0 p4 p2 p6 : Prop)
theorem file76_129776 : ((((((p2 → False) ∧ (p1 → p0)) ∧ ((p1 → p6) ∨ (p4 → False))) → False) ∧ ((((True ∨ p2) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((True ∨ p2) → False) → False) := by
      intro assump_9
      have assump_20 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


