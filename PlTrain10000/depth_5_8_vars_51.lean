variable (p4 p6 p5 p3 p1 p0 : Prop)
theorem file51_44 : (((((False ∧ p6) ∨ (p3 ∧ True)) → False) ∨ (((p4 → False) → False) → False)) → ((((p1 ∧ False) ∧ (False → False)) → False) ∨ (((p0 → p5) ∨ (p5 → True)) → ((p0 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  case inr assump_3 =>
    apply Or.inl
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_21


variable (p7 p3 p2 p6 p1 p0 : Prop)
theorem file51_748 : (((((p1 ∧ p2) ∧ (p0 → False)) → False) → False) → ((((p2 ∨ True) → False) → ((p3 ∨ p7) → False)) ∨ (((True → p0) ∨ (p6 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    have assump_24 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_4 assump_24
    apply False.elim assump_12
  case inr assump_7 =>
    have assump_25 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_20 := assump_4 assump_25
    apply False.elim assump_20


variable (p7 p0 p5 p1 p2 : Prop)
theorem file51_1384 : ((((((p7 → False) → (False → p7)) → ((p0 → p5) ∧ (p0 → p1))) → (((False ∧ p7) → False) ∨ ((p7 → p1) → (p2 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 → False) → (False → p7)) → ((p0 → p5) ∧ (p0 → p1))) → (((False ∧ p7) → False) ∨ ((p7 → p1) → (p2 ∧ True)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p1 p7 p3 p2 p4 p5 p0 : Prop)
theorem file51_1956 : (((((p6 ∧ p7) → False) → False) ∧ (((p0 ∧ True) → False) ∧ ((True → p3) ∧ (False ∧ p4)))) → ((((p0 ∨ p7) ∨ (p6 ∧ p1)) → ((p2 ∧ False) ∨ (False ∧ p5))) ∧ (((p7 → p7) ∨ (p1 ∧ p5)) → ((p0 → p2) → (p1 ∧ p5))))) := by
  intro assump_17
  apply And.intro
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    cases assump_19
    case inl assump_21 =>
      cases assump_17
      case intro assump_25 assump_26 =>
        cases assump_26
        case intro assump_29 assump_30 =>
          cases assump_30
          case intro assump_33 assump_34 =>
            cases assump_34
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
    case inr assump_22 =>
      cases assump_17
      case intro assump_43 assump_44 =>
        cases assump_44
        case intro assump_47 assump_48 =>
          cases assump_48
          case intro assump_51 assump_52 =>
            cases assump_52
            case intro assump_55 assump_56 =>
              apply False.elim assump_55
  case inr assump_20 =>
    cases assump_20
    case intro assump_59 assump_60 =>
      cases assump_17
      case intro assump_65 assump_66 =>
        cases assump_66
        case intro assump_69 assump_70 =>
          cases assump_70
          case intro assump_73 assump_74 =>
            cases assump_74
            case intro assump_77 assump_78 =>
              apply False.elim assump_77
  intro assump_81
  intro assump_82
  apply And.intro
  cases assump_81
  case inl assump_85 =>
    cases assump_17
    case intro assump_89 assump_90 =>
      cases assump_90
      case intro assump_93 assump_94 =>
        cases assump_94
        case intro assump_97 assump_98 =>
          cases assump_98
          case intro assump_101 assump_102 =>
            apply False.elim assump_101
  case inr assump_86 =>
    cases assump_86
    case intro assump_105 assump_106 =>
      cases assump_17
      case intro assump_111 assump_112 =>
        cases assump_112
        case intro assump_115 assump_116 =>
          cases assump_116
          case intro assump_119 assump_120 =>
            cases assump_120
            case intro assump_123 assump_124 =>
              apply False.elim assump_123
  cases assump_81
  case inl assump_129 =>
    cases assump_17
    case intro assump_133 assump_134 =>
      cases assump_134
      case intro assump_137 assump_138 =>
        cases assump_138
        case intro assump_141 assump_142 =>
          cases assump_142
          case intro assump_145 assump_146 =>
            apply False.elim assump_145
  case inr assump_130 =>
    cases assump_130
    case intro assump_149 assump_150 =>
      cases assump_17
      case intro assump_155 assump_156 =>
        cases assump_156
        case intro assump_159 assump_160 =>
          cases assump_160
          case intro assump_163 assump_164 =>
            cases assump_164
            case intro assump_167 assump_168 =>
              apply False.elim assump_167


variable (p4 p2 p7 p0 p6 p1 : Prop)
theorem file51_4982 : (((((p4 → p1) → False) → False) ∧ (((p7 → False) → (True ∨ p2)) → False)) → ((((p1 ∧ p6) → False) → False) → (((p0 → True) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    have assump_21 : ((p7 → False) → (True ∨ p2)) := by
      intro assump_15
      apply Or.inl
      apply True.intro
    let assump_14 := assump_9 assump_21
    apply False.elim assump_14


variable (p0 p3 p4 p5 p2 p1 p7 p6 : Prop)
theorem file51_5490 : (((((p2 → False) → False) → False) ∧ (((True → p0) ∨ (p4 → p4)) ∧ ((p5 ∨ p3) → (p7 → p1)))) → ((((p7 ∧ p2) ∧ (p2 → False)) → False) ∨ (((p1 ∨ p5) ∧ (p7 → p0)) ∧ ((p0 → p3) ∨ (p6 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            have assump_48 : p2 := by
              exact assump_18
            let assump_25 := assump_16 assump_48
            apply False.elim assump_25
      case inr assump_9 =>
        apply Or.inl
        intro assump_33
        cases assump_33
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            have assump_49 : p2 := by
              exact assump_37
            let assump_44 := assump_35 assump_49
            apply False.elim assump_44


variable (p2 p1 p6 p0 p4 p7 p3 p5 : Prop)
theorem file51_6625 : (((((p7 ∧ True) ∨ (p1 ∨ p6)) ∧ ((p2 → False) ∨ (p2 ∨ False))) ∨ (((p4 ∨ False) ∧ (p1 → True)) → False)) → ((((p4 → False) ∨ (True ∧ True)) ∧ ((True ∧ False) ∨ (p5 ∨ p3))) → (((p7 ∧ False) → (p7 ∨ p2)) ∨ ((p1 → False) → (p5 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_12
      case inr assump_10 =>
        cases assump_10
        case inl assump_17 =>
          cases assump_1
          case inl assump_21 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_23
              case inl assump_25 =>
                cases assump_25
                case intro assump_27 assump_28 =>
                  cases assump_24
                  case inl assump_33 =>
                    apply Or.inl
                    intro assump_37
                    cases assump_37
                    case intro assump_38 assump_39 =>
                      apply False.elim assump_39
                  case inr assump_34 =>
                    cases assump_34
                    case inl assump_44 =>
                      apply Or.inl
                      intro assump_48
                      cases assump_48
                      case intro assump_49 assump_50 =>
                        apply False.elim assump_50
                    case inr assump_45 =>
                      apply False.elim assump_45
              case inr assump_26 =>
                cases assump_26
                case inl assump_57 =>
                  cases assump_24
                  case inl assump_61 =>
                    apply Or.inl
                    intro assump_65
                    cases assump_65
                    case intro assump_66 assump_67 =>
                      apply False.elim assump_67
                  case inr assump_62 =>
                    cases assump_62
                    case inl assump_72 =>
                      apply Or.inl
                      intro assump_76
                      cases assump_76
                      case intro assump_77 assump_78 =>
                        apply False.elim assump_78
                    case inr assump_73 =>
                      apply False.elim assump_73
                case inr assump_58 =>
                  cases assump_24
                  case inl assump_87 =>
                    apply Or.inl
                    intro assump_91
                    cases assump_91
                    case intro assump_92 assump_93 =>
                      apply False.elim assump_93
                  case inr assump_88 =>
                    cases assump_88
                    case inl assump_98 =>
                      apply Or.inl
                      intro assump_102
                      cases assump_102
                      case intro assump_103 assump_104 =>
                        apply False.elim assump_104
                    case inr assump_99 =>
                      apply False.elim assump_99
          case inr assump_22 =>
            apply Or.inl
            intro assump_113
            cases assump_113
            case intro assump_114 assump_115 =>
              apply False.elim assump_115
        case inr assump_18 =>
          cases assump_1
          case inl assump_122 =>
            cases assump_122
            case intro assump_124 assump_125 =>
              cases assump_124
              case inl assump_126 =>
                cases assump_126
                case intro assump_128 assump_129 =>
                  cases assump_125
                  case inl assump_134 =>
                    apply Or.inl
                    intro assump_138
                    cases assump_138
                    case intro assump_139 assump_140 =>
                      apply False.elim assump_140
                  case inr assump_135 =>
                    cases assump_135
                    case inl assump_145 =>
                      apply Or.inl
                      intro assump_149
                      cases assump_149
                      case intro assump_150 assump_151 =>
                        apply False.elim assump_151
                    case inr assump_146 =>
                      apply False.elim assump_146
              case inr assump_127 =>
                cases assump_127
                case inl assump_158 =>
                  cases assump_125
                  case inl assump_162 =>
                    apply Or.inl
                    intro assump_166
                    cases assump_166
                    case intro assump_167 assump_168 =>
                      apply False.elim assump_168
                  case inr assump_163 =>
                    cases assump_163
                    case inl assump_173 =>
                      apply Or.inl
                      intro assump_177
                      cases assump_177
                      case intro assump_178 assump_179 =>
                        apply False.elim assump_179
                    case inr assump_174 =>
                      apply False.elim assump_174
                case inr assump_159 =>
                  cases assump_125
                  case inl assump_188 =>
                    apply Or.inl
                    intro assump_192
                    cases assump_192
                    case intro assump_193 assump_194 =>
                      apply False.elim assump_194
                  case inr assump_189 =>
                    cases assump_189
                    case inl assump_199 =>
                      apply Or.inl
                      intro assump_203
                      cases assump_203
                      case intro assump_204 assump_205 =>
                        apply False.elim assump_205
                    case inr assump_200 =>
                      apply False.elim assump_200
          case inr assump_123 =>
            apply Or.inl
            intro assump_214
            cases assump_214
            case intro assump_215 assump_216 =>
              apply False.elim assump_216
    case inr assump_6 =>
      cases assump_6
      case intro assump_221 assump_222 =>
        cases assump_4
        case inl assump_227 =>
          cases assump_227
          case intro assump_229 assump_230 =>
            apply False.elim assump_230
        case inr assump_228 =>
          cases assump_228
          case inl assump_235 =>
            cases assump_1
            case inl assump_239 =>
              cases assump_239
              case intro assump_241 assump_242 =>
                cases assump_241
                case inl assump_243 =>
                  cases assump_243
                  case intro assump_245 assump_246 =>
                    cases assump_242
                    case inl assump_251 =>
                      apply Or.inl
                      intro assump_255
                      cases assump_255
                      case intro assump_256 assump_257 =>
                        apply False.elim assump_257
                    case inr assump_252 =>
                      cases assump_252
                      case inl assump_262 =>
                        apply Or.inl
                        intro assump_266
                        cases assump_266
                        case intro assump_267 assump_268 =>
                          apply False.elim assump_268
                      case inr assump_263 =>
                        apply False.elim assump_263
                case inr assump_244 =>
                  cases assump_244
                  case inl assump_275 =>
                    cases assump_242
                    case inl assump_279 =>
                      apply Or.inl
                      intro assump_283
                      cases assump_283
                      case intro assump_284 assump_285 =>
                        apply False.elim assump_285
                    case inr assump_280 =>
                      cases assump_280
                      case inl assump_290 =>
                        apply Or.inl
                        intro assump_294
                        cases assump_294
                        case intro assump_295 assump_296 =>
                          apply False.elim assump_296
                      case inr assump_291 =>
                        apply False.elim assump_291
                  case inr assump_276 =>
                    cases assump_242
                    case inl assump_305 =>
                      apply Or.inl
                      intro assump_309
                      cases assump_309
                      case intro assump_310 assump_311 =>
                        apply False.elim assump_311
                    case inr assump_306 =>
                      cases assump_306
                      case inl assump_316 =>
                        apply Or.inl
                        intro assump_320
                        cases assump_320
                        case intro assump_321 assump_322 =>
                          apply False.elim assump_322
                      case inr assump_317 =>
                        apply False.elim assump_317
            case inr assump_240 =>
              apply Or.inl
              intro assump_331
              cases assump_331
              case intro assump_332 assump_333 =>
                apply False.elim assump_333
          case inr assump_236 =>
            cases assump_1
            case inl assump_340 =>
              cases assump_340
              case intro assump_342 assump_343 =>
                cases assump_342
                case inl assump_344 =>
                  cases assump_344
                  case intro assump_346 assump_347 =>
                    cases assump_343
                    case inl assump_352 =>
                      apply Or.inl
                      intro assump_356
                      cases assump_356
                      case intro assump_357 assump_358 =>
                        apply False.elim assump_358
                    case inr assump_353 =>
                      cases assump_353
                      case inl assump_363 =>
                        apply Or.inl
                        intro assump_367
                        cases assump_367
                        case intro assump_368 assump_369 =>
                          apply False.elim assump_369
                      case inr assump_364 =>
                        apply False.elim assump_364
                case inr assump_345 =>
                  cases assump_345
                  case inl assump_376 =>
                    cases assump_343
                    case inl assump_380 =>
                      apply Or.inl
                      intro assump_384
                      cases assump_384
                      case intro assump_385 assump_386 =>
                        apply False.elim assump_386
                    case inr assump_381 =>
                      cases assump_381
                      case inl assump_391 =>
                        apply Or.inl
                        intro assump_395
                        cases assump_395
                        case intro assump_396 assump_397 =>
                          apply False.elim assump_397
                      case inr assump_392 =>
                        apply False.elim assump_392
                  case inr assump_377 =>
                    cases assump_343
                    case inl assump_406 =>
                      apply Or.inl
                      intro assump_410
                      cases assump_410
                      case intro assump_411 assump_412 =>
                        apply False.elim assump_412
                    case inr assump_407 =>
                      cases assump_407
                      case inl assump_417 =>
                        apply Or.inl
                        intro assump_421
                        cases assump_421
                        case intro assump_422 assump_423 =>
                          apply False.elim assump_423
                      case inr assump_418 =>
                        apply False.elim assump_418
            case inr assump_341 =>
              apply Or.inl
              intro assump_432
              cases assump_432
              case intro assump_433 assump_434 =>
                apply False.elim assump_434


variable (p2 p4 p1 : Prop)
theorem file51_19181 : ((((((p4 → False) ∧ (p4 ∧ p4)) ∧ ((p1 ∧ p2) → False)) → False) → False) → False) := by
  intro assump_5
  have assump_34 : ((((p4 → False) ∧ (p4 ∧ p4)) ∧ ((p1 ∧ p2) → False)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          have assump_35 : p4 := by
            exact assump_17
          let assump_27 := assump_12 assump_35
          apply False.elim assump_27
  let assump_8 := assump_5 assump_34
  apply False.elim assump_8


variable (p2 p0 p5 p6 p4 p3 : Prop)
theorem file51_19848 : (((((p4 ∧ p6) ∧ (p5 ∨ p0)) → ((p0 ∨ p2) → (p3 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_44 : (((p4 ∧ p6) ∧ (p5 ∨ p0)) → ((p0 ∨ p2) → (p3 ∨ p4))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case inl assump_19 =>
            apply Or.inr
            exact assump_13
          case inr assump_20 =>
            apply Or.inr
            exact assump_13
    case inr assump_8 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_28
          case inl assump_35 =>
            apply Or.inr
            exact assump_29
          case inr assump_36 =>
            apply Or.inr
            exact assump_29
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p5 p6 p0 p4 p3 : Prop)
theorem file51_20895 : (((((p4 ∨ p6) ∨ (p0 ∨ True)) → False) ∧ (((False → False) → False) ∧ ((p0 ∧ p0) → (p3 → p5)))) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      have assump_43 : (False → False) := by
        intro assump_37
        apply False.elim assump_37
      let assump_36 := assump_29 assump_43
      apply False.elim assump_36


variable (p2 p6 p3 p0 p7 p5 : Prop)
theorem file51_21375 : ((((((p6 ∨ p2) ∧ (p5 → False)) ∨ ((False ∨ p7) → False)) ∨ (((p7 ∧ True) ∨ (p0 → False)) ∨ ((p3 ∨ p0) ∧ (p7 → False)))) ∧ ((((False ∨ True) ∨ (p7 → p7)) → False) ∧ (((p5 ∧ p0) ∧ (False ∨ p0)) → False))) → False) := by
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
            cases assump_3
            case intro assump_16 assump_17 =>
              have assump_123 : ((False ∨ True) ∨ (p7 → p7)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_23 := assump_16 assump_123
              apply False.elim assump_23
          case inr assump_11 =>
            cases assump_3
            case intro assump_31 assump_32 =>
              have assump_124 : ((False ∨ True) ∨ (p7 → p7)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_38 := assump_31 assump_124
              apply False.elim assump_38
      case inr assump_7 =>
        cases assump_3
        case intro assump_44 assump_45 =>
          have assump_125 : ((False ∨ True) ∨ (p7 → p7)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_51 := assump_44 assump_125
          apply False.elim assump_51
    case inr assump_5 =>
      cases assump_5
      case inl assump_55 =>
        cases assump_55
        case inl assump_57 =>
          cases assump_57
          case intro assump_59 assump_60 =>
            cases assump_3
            case intro assump_65 assump_66 =>
              have assump_126 : ((False ∨ True) ∨ (p7 → p7)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_72 := assump_65 assump_126
              apply False.elim assump_72
        case inr assump_58 =>
          cases assump_3
          case intro assump_78 assump_79 =>
            have assump_127 : ((False ∨ True) ∨ (p7 → p7)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_85 := assump_78 assump_127
            apply False.elim assump_85
      case inr assump_56 =>
        cases assump_56
        case intro assump_89 assump_90 =>
          cases assump_89
          case inl assump_91 =>
            cases assump_3
            case intro assump_97 assump_98 =>
              have assump_128 : ((False ∨ True) ∨ (p7 → p7)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_104 := assump_97 assump_128
              apply False.elim assump_104
          case inr assump_92 =>
            cases assump_3
            case intro assump_112 assump_113 =>
              have assump_129 : ((False ∨ True) ∨ (p7 → p7)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_119 := assump_112 assump_129
              apply False.elim assump_119


variable (p5 p0 p6 p7 p2 p4 : Prop)
theorem file51_24631 : ((((((p4 ∨ p6) ∧ (p6 ∨ False)) ∨ ((p0 → True) ∧ (p0 ∨ p0))) ∧ (((p0 ∧ p0) ∧ (p6 ∨ p6)) ∧ ((False → False) ∨ (p6 → p4)))) ∧ ((((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) → False)) → False) := by
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
          case inl assump_10 =>
            cases assump_9
            case inl assump_14 =>
              cases assump_5
              case intro assump_18 assump_19 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  cases assump_20
                  case intro assump_22 assump_23 =>
                    cases assump_21
                    case inl assump_28 =>
                      cases assump_19
                      case inl assump_32 =>
                        have assump_582 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_39
                          intro assump_40
                          cases assump_39
                          case inl assump_43 =>
                            have assump_583 : p6 := by
                              exact assump_28
                            let assump_49 := assump_40 assump_583
                            apply False.elim assump_49
                          case inr assump_44 =>
                            have assump_584 : p6 := by
                              exact assump_28
                            let assump_56 := assump_40 assump_584
                            apply False.elim assump_56
                        let assump_38 := assump_3 assump_582
                        apply False.elim assump_38
                      case inr assump_33 =>
                        have assump_585 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_68
                          intro assump_69
                          cases assump_68
                          case inl assump_72 =>
                            have assump_586 : p6 := by
                              exact assump_28
                            let assump_78 := assump_69 assump_586
                            apply False.elim assump_78
                          case inr assump_73 =>
                            have assump_587 : p6 := by
                              exact assump_28
                            let assump_85 := assump_69 assump_587
                            apply False.elim assump_85
                        let assump_67 := assump_3 assump_585
                        apply False.elim assump_67
                    case inr assump_29 =>
                      cases assump_19
                      case inl assump_94 =>
                        have assump_588 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_101
                          intro assump_102
                          cases assump_101
                          case inl assump_105 =>
                            have assump_589 : p6 := by
                              exact assump_29
                            let assump_111 := assump_102 assump_589
                            apply False.elim assump_111
                          case inr assump_106 =>
                            have assump_590 : p6 := by
                              exact assump_29
                            let assump_118 := assump_102 assump_590
                            apply False.elim assump_118
                        let assump_100 := assump_3 assump_588
                        apply False.elim assump_100
                      case inr assump_95 =>
                        have assump_591 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_130
                          intro assump_131
                          cases assump_130
                          case inl assump_134 =>
                            have assump_592 : p6 := by
                              exact assump_29
                            let assump_140 := assump_131 assump_592
                            apply False.elim assump_140
                          case inr assump_135 =>
                            have assump_593 : p6 := by
                              exact assump_29
                            let assump_147 := assump_131 assump_593
                            apply False.elim assump_147
                        let assump_129 := assump_3 assump_591
                        apply False.elim assump_129
            case inr assump_15 =>
              apply False.elim assump_15
          case inr assump_11 =>
            cases assump_9
            case inl assump_158 =>
              cases assump_5
              case intro assump_162 assump_163 =>
                cases assump_162
                case intro assump_164 assump_165 =>
                  cases assump_164
                  case intro assump_166 assump_167 =>
                    cases assump_165
                    case inl assump_172 =>
                      cases assump_163
                      case inl assump_176 =>
                        have assump_594 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_183
                          intro assump_184
                          cases assump_183
                          case inl assump_187 =>
                            have assump_595 : p6 := by
                              exact assump_172
                            let assump_193 := assump_184 assump_595
                            apply False.elim assump_193
                          case inr assump_188 =>
                            have assump_596 : p6 := by
                              exact assump_172
                            let assump_200 := assump_184 assump_596
                            apply False.elim assump_200
                        let assump_182 := assump_3 assump_594
                        apply False.elim assump_182
                      case inr assump_177 =>
                        have assump_597 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_212
                          intro assump_213
                          cases assump_212
                          case inl assump_216 =>
                            have assump_598 : p6 := by
                              exact assump_172
                            let assump_222 := assump_213 assump_598
                            apply False.elim assump_222
                          case inr assump_217 =>
                            have assump_599 : p6 := by
                              exact assump_172
                            let assump_229 := assump_213 assump_599
                            apply False.elim assump_229
                        let assump_211 := assump_3 assump_597
                        apply False.elim assump_211
                    case inr assump_173 =>
                      cases assump_163
                      case inl assump_238 =>
                        have assump_600 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_245
                          intro assump_246
                          cases assump_245
                          case inl assump_249 =>
                            have assump_601 : p6 := by
                              exact assump_173
                            let assump_255 := assump_246 assump_601
                            apply False.elim assump_255
                          case inr assump_250 =>
                            have assump_602 : p6 := by
                              exact assump_173
                            let assump_262 := assump_246 assump_602
                            apply False.elim assump_262
                        let assump_244 := assump_3 assump_600
                        apply False.elim assump_244
                      case inr assump_239 =>
                        have assump_603 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                          intro assump_274
                          intro assump_275
                          cases assump_274
                          case inl assump_278 =>
                            have assump_604 : p6 := by
                              exact assump_173
                            let assump_284 := assump_275 assump_604
                            apply False.elim assump_284
                          case inr assump_279 =>
                            have assump_605 : p6 := by
                              exact assump_173
                            let assump_291 := assump_275 assump_605
                            apply False.elim assump_291
                        let assump_273 := assump_3 assump_603
                        apply False.elim assump_273
            case inr assump_159 =>
              apply False.elim assump_159
      case inr assump_7 =>
        cases assump_7
        case intro assump_300 assump_301 =>
          cases assump_301
          case inl assump_304 =>
            cases assump_5
            case intro assump_308 assump_309 =>
              cases assump_308
              case intro assump_310 assump_311 =>
                cases assump_310
                case intro assump_312 assump_313 =>
                  cases assump_311
                  case inl assump_318 =>
                    cases assump_309
                    case inl assump_322 =>
                      have assump_606 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_329
                        intro assump_330
                        cases assump_329
                        case inl assump_333 =>
                          have assump_607 : p6 := by
                            exact assump_318
                          let assump_339 := assump_330 assump_607
                          apply False.elim assump_339
                        case inr assump_334 =>
                          have assump_608 : p6 := by
                            exact assump_318
                          let assump_346 := assump_330 assump_608
                          apply False.elim assump_346
                      let assump_328 := assump_3 assump_606
                      apply False.elim assump_328
                    case inr assump_323 =>
                      have assump_609 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_358
                        intro assump_359
                        cases assump_358
                        case inl assump_362 =>
                          have assump_610 : p6 := by
                            exact assump_318
                          let assump_368 := assump_359 assump_610
                          apply False.elim assump_368
                        case inr assump_363 =>
                          have assump_611 : p6 := by
                            exact assump_318
                          let assump_375 := assump_359 assump_611
                          apply False.elim assump_375
                      let assump_357 := assump_3 assump_609
                      apply False.elim assump_357
                  case inr assump_319 =>
                    cases assump_309
                    case inl assump_384 =>
                      have assump_612 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_391
                        intro assump_392
                        cases assump_391
                        case inl assump_395 =>
                          have assump_613 : p6 := by
                            exact assump_319
                          let assump_401 := assump_392 assump_613
                          apply False.elim assump_401
                        case inr assump_396 =>
                          have assump_614 : p6 := by
                            exact assump_319
                          let assump_408 := assump_392 assump_614
                          apply False.elim assump_408
                      let assump_390 := assump_3 assump_612
                      apply False.elim assump_390
                    case inr assump_385 =>
                      have assump_615 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_420
                        intro assump_421
                        cases assump_420
                        case inl assump_424 =>
                          have assump_616 : p6 := by
                            exact assump_319
                          let assump_430 := assump_421 assump_616
                          apply False.elim assump_430
                        case inr assump_425 =>
                          have assump_617 : p6 := by
                            exact assump_319
                          let assump_437 := assump_421 assump_617
                          apply False.elim assump_437
                      let assump_419 := assump_3 assump_615
                      apply False.elim assump_419
          case inr assump_305 =>
            cases assump_5
            case intro assump_446 assump_447 =>
              cases assump_446
              case intro assump_448 assump_449 =>
                cases assump_448
                case intro assump_450 assump_451 =>
                  cases assump_449
                  case inl assump_456 =>
                    cases assump_447
                    case inl assump_460 =>
                      have assump_618 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_467
                        intro assump_468
                        cases assump_467
                        case inl assump_471 =>
                          have assump_619 : p6 := by
                            exact assump_456
                          let assump_477 := assump_468 assump_619
                          apply False.elim assump_477
                        case inr assump_472 =>
                          have assump_620 : p6 := by
                            exact assump_456
                          let assump_484 := assump_468 assump_620
                          apply False.elim assump_484
                      let assump_466 := assump_3 assump_618
                      apply False.elim assump_466
                    case inr assump_461 =>
                      have assump_621 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_496
                        intro assump_497
                        cases assump_496
                        case inl assump_500 =>
                          have assump_622 : p6 := by
                            exact assump_456
                          let assump_506 := assump_497 assump_622
                          apply False.elim assump_506
                        case inr assump_501 =>
                          have assump_623 : p6 := by
                            exact assump_456
                          let assump_513 := assump_497 assump_623
                          apply False.elim assump_513
                      let assump_495 := assump_3 assump_621
                      apply False.elim assump_495
                  case inr assump_457 =>
                    cases assump_447
                    case inl assump_522 =>
                      have assump_624 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_529
                        intro assump_530
                        cases assump_529
                        case inl assump_533 =>
                          have assump_625 : p6 := by
                            exact assump_457
                          let assump_539 := assump_530 assump_625
                          apply False.elim assump_539
                        case inr assump_534 =>
                          have assump_626 : p6 := by
                            exact assump_457
                          let assump_546 := assump_530 assump_626
                          apply False.elim assump_546
                      let assump_528 := assump_3 assump_624
                      apply False.elim assump_528
                    case inr assump_523 =>
                      have assump_627 : (((True → p7) ∨ (p2 → p5)) → ((p6 → False) → False)) := by
                        intro assump_558
                        intro assump_559
                        cases assump_558
                        case inl assump_562 =>
                          have assump_628 : p6 := by
                            exact assump_457
                          let assump_568 := assump_559 assump_628
                          apply False.elim assump_568
                        case inr assump_563 =>
                          have assump_629 : p6 := by
                            exact assump_457
                          let assump_575 := assump_559 assump_629
                          apply False.elim assump_575
                      let assump_557 := assump_3 assump_627
                      apply False.elim assump_557


variable (p3 p6 p1 p7 p4 : Prop)
theorem file51_42148 : ((((((False → False) ∧ (p1 → False)) ∧ ((False ∧ True) ∧ (p1 → False))) → (((False → False) ∨ (p3 ∧ p7)) ∨ ((True → True) ∧ (p4 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → False) ∧ (p1 → False)) ∧ ((False ∧ True) ∧ (p1 → False))) → (((False → False) ∨ (p3 ∧ p7)) ∨ ((True → True) ∧ (p4 ∧ p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p4 p7 p6 p5 p3 p1 p0 : Prop)
theorem file51_42924 : (((((True ∧ p7) → False) ∧ ((p4 → p5) ∨ (p5 ∧ p6))) ∨ (((False → False) ∨ (p2 → p3)) ∨ ((True ∨ p3) ∧ (p0 → False)))) → ((((True ∨ p1) ∧ (False ∧ p6)) → False) ∨ (((p2 ∨ True) ∨ (p0 ∧ p5)) → ((p5 → False) ∨ (False ∨ p7))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_14
            case intro assump_19 assump_20 =>
              apply False.elim assump_19
          case inr assump_16 =>
            cases assump_14
            case intro assump_25 assump_26 =>
              apply False.elim assump_25
      case inr assump_9 =>
        cases assump_9
        case intro assump_29 assump_30 =>
          apply Or.inl
          intro assump_35
          cases assump_35
          case intro assump_36 assump_37 =>
            cases assump_36
            case inl assump_38 =>
              cases assump_37
              case intro assump_42 assump_43 =>
                apply False.elim assump_42
            case inr assump_39 =>
              cases assump_37
              case intro assump_48 assump_49 =>
                apply False.elim assump_48
  case inr assump_3 =>
    cases assump_3
    case inl assump_52 =>
      cases assump_52
      case inl assump_54 =>
        apply Or.inl
        intro assump_58
        cases assump_58
        case intro assump_59 assump_60 =>
          cases assump_59
          case inl assump_61 =>
            cases assump_60
            case intro assump_65 assump_66 =>
              apply False.elim assump_65
          case inr assump_62 =>
            cases assump_60
            case intro assump_71 assump_72 =>
              apply False.elim assump_71
      case inr assump_55 =>
        apply Or.inl
        intro assump_77
        cases assump_77
        case intro assump_78 assump_79 =>
          cases assump_78
          case inl assump_80 =>
            cases assump_79
            case intro assump_84 assump_85 =>
              apply False.elim assump_84
          case inr assump_81 =>
            cases assump_79
            case intro assump_90 assump_91 =>
              apply False.elim assump_90
    case inr assump_53 =>
      cases assump_53
      case intro assump_94 assump_95 =>
        cases assump_94
        case inl assump_96 =>
          apply Or.inl
          intro assump_102
          cases assump_102
          case intro assump_103 assump_104 =>
            cases assump_103
            case inl assump_105 =>
              cases assump_104
              case intro assump_109 assump_110 =>
                apply False.elim assump_109
            case inr assump_106 =>
              cases assump_104
              case intro assump_115 assump_116 =>
                apply False.elim assump_115
        case inr assump_97 =>
          apply Or.inl
          intro assump_123
          cases assump_123
          case intro assump_124 assump_125 =>
            cases assump_124
            case inl assump_126 =>
              cases assump_125
              case intro assump_130 assump_131 =>
                apply False.elim assump_130
            case inr assump_127 =>
              cases assump_125
              case intro assump_136 assump_137 =>
                apply False.elim assump_136


variable (p4 p2 : Prop)
theorem file51_46466 : ((((((p2 ∨ True) ∨ (p4 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∨ True) ∨ (p4 → False)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p2 ∨ True) ∨ (p4 → False)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p7 p5 p0 p4 : Prop)
theorem file51_46959 : (((((p1 ∨ p0) → (p5 → p5)) ∨ ((p7 ∧ p0) ∨ (p4 → p5))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p1 ∨ p0) → (p5 → p5)) ∨ ((p7 ∧ p0) ∨ (p4 → p5))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      exact assump_6
    case inr assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p6 p4 p1 : Prop)
theorem file51_47417 : ((((((False ∨ False) → (p3 → False)) → ((p1 → p4) → False)) → False) ∧ ((((False → p6) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → p6) → False) → False) := by
      intro assump_9
      have assump_23 : (False → p6) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p4 p2 : Prop)
theorem file51_47989 : ((((((False → False) ∨ (p2 ∧ p4)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) ∨ (p2 ∧ p4)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → False) ∨ (p2 ∧ p4)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p1 p4 p5 : Prop)
theorem file51_48493 : ((((((False → False) ∧ (p1 ∨ False)) ∧ ((p5 → False) → False)) ∨ (((False → False) ∨ (p4 → False)) ∨ ((p2 → False) ∧ (True ∧ p2)))) → ((((p4 → p4) → False) → False) → False)) → False) := by
  intro assump_1
  have assump_25 : ((((False → False) ∧ (p1 ∨ False)) ∧ ((p5 → False) → False)) ∨ (((False → False) ∨ (p4 → False)) ∨ ((p2 → False) ∧ (True ∧ p2)))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  have assump_26 : (((p4 → p4) → False) → False) := by
    intro assump_12
    have assump_27 : (p4 → p4) := by
      intro assump_16
      exact assump_16
    let assump_15 := assump_12 assump_27
    apply False.elim assump_15
  let assump_11 := assump_4 assump_26
  apply False.elim assump_11


variable (p3 p7 p1 p5 p0 p6 p4 : Prop)
theorem file51_49350 : ((((((True ∧ p6) → (False ∨ True)) ∨ ((p6 ∧ p7) → (p1 ∨ p3))) → False) ∧ ((((p4 → p3) ∧ (p5 ∧ p5)) → ((False ∧ p0) ∨ (p6 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p4 → p3) ∧ (p5 ∧ p5)) → ((False ∧ p0) ∨ (p6 → True))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply Or.inr
          intro assump_20
          apply True.intro
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p5 p2 p1 p4 p7 p3 : Prop)
theorem file51_50011 : (((((False ∧ p3) → (p7 ∧ p1)) → False) → False) ∨ ((((p4 ∧ p2) → False) ∨ ((p1 ∧ p4) ∧ (p2 → False))) → (((True → p3) ∧ (p4 → p5)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_17 : ((False ∧ p3) → (p7 ∧ p1)) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    cases assump_5
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p6 p4 p3 p7 p2 : Prop)
theorem file51_50581 : ((((((p7 → p4) ∨ (p2 ∧ True)) ∨ ((p3 → p3) → (p3 → True))) → (((False → p6) → False) → False)) ∧ ((((True → False) → (p7 → False)) ∨ ((p2 ∨ True) → False)) → False)) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    have assump_41 : (((True → False) → (p7 → False)) ∨ ((p2 ∨ True) → False)) := by
      apply Or.inl
      intro assump_28
      intro assump_29
      have assump_42 : True := by
        apply True.intro
      let assump_34 := assump_28 assump_42
      apply False.elim assump_34
    let assump_27 := assump_22 assump_41
    apply False.elim assump_27


variable (p1 p5 p7 p6 p0 p2 p4 : Prop)
theorem file51_51252 : (((((p7 ∧ p4) → False) → ((True ∧ p0) → (p0 → True))) → False) → ((((p2 ∨ p2) → False) ∧ ((p6 → False) ∧ (p7 ∨ True))) ∧ (((p4 ∨ False) → (p1 ∧ p5)) ∧ ((p1 ∧ True) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_88 : (((p7 ∧ p4) → False) → ((True ∧ p0) → (p0 → True))) := by
      intro assump_10
      intro assump_11
      intro assump_12
      apply True.intro
    let assump_9 := assump_1 assump_88
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_89 : (((p7 ∧ p4) → False) → ((True ∧ p0) → (p0 → True))) := by
      intro assump_21
      intro assump_22
      intro assump_23
      apply True.intro
    let assump_20 := assump_1 assump_89
    apply False.elim assump_20
  apply And.intro
  intro assump_27
  have assump_90 : (((p7 ∧ p4) → False) → ((True ∧ p0) → (p0 → True))) := by
    intro assump_33
    intro assump_34
    intro assump_35
    apply True.intro
  let assump_32 := assump_1 assump_90
  apply False.elim assump_32
  apply Or.inr
  apply True.intro
  apply And.intro
  intro assump_41
  apply And.intro
  cases assump_41
  case inl assump_42 =>
    have assump_91 : (((p7 ∧ p4) → False) → ((True ∧ p0) → (p0 → True))) := by
      intro assump_49
      intro assump_50
      intro assump_51
      apply True.intro
    let assump_48 := assump_1 assump_91
    apply False.elim assump_48
  case inr assump_43 =>
    apply False.elim assump_43
  cases assump_41
  case inl assump_57 =>
    have assump_92 : (((p7 ∧ p4) → False) → ((True ∧ p0) → (p0 → True))) := by
      intro assump_64
      intro assump_65
      intro assump_66
      apply True.intro
    let assump_63 := assump_1 assump_92
    apply False.elim assump_63
  case inr assump_58 =>
    apply False.elim assump_58
  intro assump_72
  cases assump_72
  case intro assump_73 assump_74 =>
    have assump_93 : (((p7 ∧ p4) → False) → ((True ∧ p0) → (p0 → True))) := by
      intro assump_82
      intro assump_83
      intro assump_84
      apply True.intro
    let assump_81 := assump_1 assump_93
    apply False.elim assump_81


variable (p5 p3 p4 p2 : Prop)
theorem file51_53429 : ((((((p2 → p2) → False) ∧ ((p5 ∨ True) ∧ (p3 ∧ p4))) → (((p4 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_55 : ((((p2 → p2) → False) ∧ ((p5 ∨ True) ∧ (p3 ∧ p4))) → (((p4 → False) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_14
          case intro assump_19 assump_20 =>
            have assump_56 : (p2 → p2) := by
              intro assump_29
              exact assump_29
            let assump_28 := assump_9 assump_56
            apply False.elim assump_28
        case inr assump_16 =>
          cases assump_14
          case intro assump_37 assump_38 =>
            have assump_57 : (p2 → p2) := by
              intro assump_46
              exact assump_46
            let assump_45 := assump_9 assump_57
            apply False.elim assump_45
  let assump_4 := assump_1 assump_55
  apply False.elim assump_4


variable (p2 p7 p0 p1 p3 p4 p6 p5 : Prop)
theorem file51_54566 : (((((p0 → False) ∧ (p7 ∧ p5)) → ((p2 → False) → (p6 → p6))) ∨ (((p4 → False) ∧ (False ∨ False)) ∧ ((p7 ∧ False) → (p4 → False)))) ∨ ((((p3 ∨ p1) → False) ∨ ((p0 → False) ∧ (p6 → p2))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      exact assump_3


variable (p3 p5 : Prop)
theorem file51_55024 : ((((((p5 ∨ p3) ∨ (p3 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p5 ∨ p3) ∨ (p3 → False)) → False) → False) := by
    intro assump_5
    have assump_24 : ((p5 ∨ p3) ∨ (p3 → False)) := by
      apply Or.inr
      intro assump_9
      have assump_25 : ((p5 ∨ p3) ∨ (p3 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_13 := assump_5 assump_25
      apply False.elim assump_13
    let assump_8 := assump_5 assump_24
    apply False.elim assump_8
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p6 p0 p5 p1 p2 p3 : Prop)
theorem file51_55692 : (((((p5 ∧ p4) ∧ (p3 ∧ p6)) ∨ ((p2 ∨ p1) → (True ∧ p4))) → False) → ((((False ∨ p0) ∧ (p3 ∧ p2)) ∨ ((False → False) ∨ (p6 → p3))) ∨ (((True ∨ p5) → False) ∧ ((p1 ∨ p1) → (p1 ∧ p5))))) := by
  intro assump_6
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_9
  apply False.elim assump_9


variable (p0 p5 p2 p6 p4 p7 p1 p3 : Prop)
theorem file51_56054 : (((((False → False) → False) → False) ∨ (((p1 → p2) → (False → False)) ∧ ((p5 → False) → (p4 ∨ p4)))) ∨ ((((p0 ∧ p1) ∧ (p3 ∧ p4)) ∨ ((True ∧ False) ∨ (p3 → False))) ∧ (((False ∨ p3) → False) → ((p7 ∨ False) → (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p4 p3 : Prop)
theorem file51_56539 : ((((((True → False) → False) → False) → (((p4 ∧ p1) ∧ (p4 → p3)) → ((p4 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((True → False) → False) → False) → (((p4 ∧ p1) ∧ (p4 → p3)) → ((p4 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_37 : ((True → False) → False) := by
          intro assump_23
          have assump_38 : True := by
            apply True.intro
          let assump_26 := assump_23 assump_38
          apply False.elim assump_26
        let assump_22 := assump_5 assump_37
        apply False.elim assump_22
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p6 p7 p2 p4 p0 p3 p1 : Prop)
theorem file51_57403 : (((((True ∨ True) ∨ (p3 → False)) → False) ∧ (((p0 ∧ p7) → False) ∧ ((p4 → p3) ∧ (p6 → False)))) → ((((p1 ∨ p4) ∧ (p6 → False)) → ((p6 ∧ p7) ∨ (p2 ∧ p1))) ∨ (((p7 → p3) ∨ (p1 → p7)) ∧ ((p0 → False) ∨ (p2 ∧ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            have assump_48 : ((True ∨ True) ∨ (p3 → False)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_30 := assump_2 assump_48
            apply False.elim assump_30
          case inr assump_20 =>
            have assump_49 : ((True ∨ True) ∨ (p3 → False)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_44 := assump_2 assump_49
            apply False.elim assump_44


variable (p1 p3 p5 p6 : Prop)
theorem file51_58540 : ((((((False ∨ p1) ∨ (p3 ∧ p5)) ∨ ((p3 → True) → (p6 ∨ True))) ∨ (((True → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False ∨ p1) ∨ (p3 ∧ p5)) ∨ ((p3 → True) → (p6 ∨ True))) ∨ (((True → False) → False) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p6 p3 p4 p7 p1 : Prop)
theorem file51_59020 : (((((p3 ∧ False) ∨ (p4 ∧ p4)) ∨ ((p6 ∧ p4) → (False → p0))) ∨ (((p3 → p3) ∨ (p6 → False)) ∧ ((p1 → False) ∧ (p7 ∧ p7)))) ∨ ((((True → False) → (p7 → p4)) ∨ ((p7 → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p6 p0 p1 p2 p4 p5 p7 : Prop)
theorem file51_59386 : (((((p6 ∧ False) → False) ∨ ((True ∨ p0) ∧ (False ∨ p2))) ∨ (((p5 ∧ p4) ∧ (p0 → p4)) → ((p1 ∨ p4) → False))) ∨ ((((p7 → True) ∨ (p5 → p0)) → ((p2 ∨ p6) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p6 p3 p7 p5 p0 : Prop)
theorem file51_59764 : ((((((False → False) ∧ (p3 → p3)) ∨ ((p3 ∧ p3) → (p7 ∧ p5))) ∧ (((p0 ∧ p3) → (p7 → p3)) ∨ ((p0 ∨ p3) ∧ (p0 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False → False) ∧ (p3 → p3)) ∨ ((p3 ∧ p3) → (p7 ∧ p5))) ∧ (((p0 ∧ p3) → (p7 → p3)) ∨ ((p0 ∨ p3) ∧ (p0 ∧ p6)))) := by
    apply And.intro
    apply Or.inl
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    exact assump_8
    apply Or.inl
    intro assump_11
    intro assump_12
    cases assump_11
    case intro assump_15 assump_16 =>
      exact assump_16
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p3 p7 p6 p4 p5 : Prop)
theorem file51_60463 : (((((p5 → False) → False) ∧ ((True ∨ p4) → (False ∨ False))) ∧ (((False ∨ p4) → False) ∧ ((p6 ∨ p3) → (p6 ∧ p4)))) → ((((p7 ∧ p6) → (p3 → False)) ∧ ((p7 → False) → (False → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          have assump_33 : (True ∨ p4) := by
            apply Or.inl
            apply True.intro
          let assump_25 := assump_12 assump_33
          cases assump_25
          case inl assump_27 =>
            apply False.elim assump_27
          case inr assump_28 =>
            apply False.elim assump_28


variable (p7 p6 p5 p2 p0 p3 p4 p1 : Prop)
theorem file51_61309 : ((((((p5 ∨ p4) → (p1 → False)) ∨ ((p3 ∨ p6) ∨ (p7 ∨ p6))) ∧ (((False → False) ∨ (p2 → p7)) → False)) ∧ ((((p3 → False) ∧ (True → False)) → ((p6 ∧ p6) → (p0 → False))) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        have assump_180 : (((p3 → False) ∧ (True → False)) → ((p6 ∧ p6) → (p0 → False))) := by
          intro assump_26
          intro assump_27
          intro assump_28
          cases assump_27
          case intro assump_31 assump_32 =>
            cases assump_26
            case intro assump_37 assump_38 =>
              have assump_181 : True := by
                apply True.intro
              let assump_43 := assump_38 assump_181
              apply False.elim assump_43
        let assump_25 := assump_14 assump_180
        apply False.elim assump_25
      case inr assump_18 =>
        cases assump_18
        case inl assump_50 =>
          cases assump_50
          case inl assump_52 =>
            have assump_182 : (((p3 → False) ∧ (True → False)) → ((p6 ∧ p6) → (p0 → False))) := by
              intro assump_61
              intro assump_62
              intro assump_63
              cases assump_62
              case intro assump_66 assump_67 =>
                cases assump_61
                case intro assump_72 assump_73 =>
                  have assump_183 : True := by
                    apply True.intro
                  let assump_78 := assump_73 assump_183
                  apply False.elim assump_78
            let assump_60 := assump_14 assump_182
            apply False.elim assump_60
          case inr assump_53 =>
            have assump_184 : (((p3 → False) ∧ (True → False)) → ((p6 ∧ p6) → (p0 → False))) := by
              intro assump_92
              intro assump_93
              intro assump_94
              cases assump_93
              case intro assump_97 assump_98 =>
                cases assump_92
                case intro assump_103 assump_104 =>
                  have assump_185 : True := by
                    apply True.intro
                  let assump_109 := assump_104 assump_185
                  apply False.elim assump_109
            let assump_91 := assump_14 assump_184
            apply False.elim assump_91
        case inr assump_51 =>
          cases assump_51
          case inl assump_116 =>
            have assump_186 : (((p3 → False) ∧ (True → False)) → ((p6 ∧ p6) → (p0 → False))) := by
              intro assump_125
              intro assump_126
              intro assump_127
              cases assump_126
              case intro assump_130 assump_131 =>
                cases assump_125
                case intro assump_136 assump_137 =>
                  have assump_187 : True := by
                    apply True.intro
                  let assump_142 := assump_137 assump_187
                  apply False.elim assump_142
            let assump_124 := assump_14 assump_186
            apply False.elim assump_124
          case inr assump_117 =>
            have assump_188 : (((p3 → False) ∧ (True → False)) → ((p6 ∧ p6) → (p0 → False))) := by
              intro assump_156
              intro assump_157
              intro assump_158
              cases assump_157
              case intro assump_161 assump_162 =>
                cases assump_156
                case intro assump_167 assump_168 =>
                  have assump_189 : True := by
                    apply True.intro
                  let assump_173 := assump_168 assump_189
                  apply False.elim assump_173
            let assump_155 := assump_14 assump_188
            apply False.elim assump_155


variable (p5 p3 p6 p1 p0 : Prop)
theorem file51_65124 : ((((((p3 ∨ p1) → (p5 → p5)) ∧ ((p6 ∧ p0) ∧ (p5 → False))) → (((p5 → False) → False) → False)) → False) → False) := by
  intro assump_57
  have assump_98 : ((((p3 ∨ p1) → (p5 → p5)) ∧ ((p6 ∧ p0) ∧ (p5 → False))) → (((p5 → False) → False) → False)) := by
    intro assump_61
    intro assump_62
    cases assump_61
    case intro assump_65 assump_66 =>
      cases assump_66
      case intro assump_69 assump_70 =>
        cases assump_69
        case intro assump_71 assump_72 =>
          have assump_99 : (p5 → False) := by
            intro assump_84
            have assump_100 : p5 := by
              exact assump_84
            let assump_88 := assump_70 assump_100
            apply False.elim assump_88
          let assump_83 := assump_62 assump_99
          apply False.elim assump_83
  let assump_60 := assump_57 assump_98
  apply False.elim assump_60


variable (p6 p1 p0 p3 p5 p4 : Prop)
theorem file51_66047 : (((((False → False) ∨ (p6 ∧ p1)) ∧ ((p5 ∧ p4) ∨ (True ∧ p0))) → (((p3 → p4) → (False → False)) ∨ ((False ∨ p0) ∨ (p3 → False)))) ∨ ((((False → False) ∨ (p0 ∨ p0)) → ((p4 → p6) ∧ (p0 → p4))) ∧ (((p3 → False) → (p3 ∨ p5)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          apply False.elim assump_17
      case inr assump_9 =>
        cases assump_9
        case intro assump_20 assump_21 =>
          apply Or.inl
          intro assump_26
          intro assump_27
          apply False.elim assump_27
    case inr assump_5 =>
      cases assump_5
      case intro assump_30 assump_31 =>
        cases assump_3
        case inl assump_36 =>
          cases assump_36
          case intro assump_38 assump_39 =>
            apply Or.inl
            intro assump_44
            intro assump_45
            apply False.elim assump_45
        case inr assump_37 =>
          cases assump_37
          case intro assump_48 assump_49 =>
            apply Or.inl
            intro assump_54
            intro assump_55
            apply False.elim assump_55


variable (p2 p4 p0 p6 p3 p5 p7 : Prop)
theorem file51_67452 : (((((p7 → p7) ∧ (p6 → False)) ∨ ((False → False) ∧ (p6 ∧ p5))) ∧ (((p2 → True) → False) → ((p3 → False) ∨ (p6 → p4)))) → ((((False → p3) ∨ (p5 → False)) ∧ ((True → False) → (p0 ∧ True))) ∨ (((p0 → False) ∨ (False → p4)) ∧ ((p5 → False) ∧ (p6 → p2))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        apply And.intro
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
        intro assump_17
        apply And.intro
        have assump_46 : True := by
          apply True.intro
        let assump_20 := assump_17 assump_46
        apply False.elim assump_20
        apply True.intro
    case inr assump_5 =>
      cases assump_5
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          apply Or.inl
          apply And.intro
          apply Or.inl
          intro assump_36
          apply False.elim assump_36
          intro assump_39
          apply And.intro
          have assump_47 : True := by
            apply True.intro
          let assump_42 := assump_39 assump_47
          apply False.elim assump_42
          apply True.intro


variable (p0 p7 p4 p5 : Prop)
theorem file51_68793 : (((((p5 → True) → (p0 → True)) ∨ ((p4 → p7) ∧ (True → False))) → False) → False) := by
  intro assump_1
  have assump_10 : (((p5 → True) → (p0 → True)) ∨ ((p4 → p7) ∧ (True → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p2 p5 p3 p7 : Prop)
theorem file51_69178 : ((((((p3 → False) ∧ (p7 → False)) → False) → (((p5 ∧ p2) ∧ (False ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p3 → False) ∧ (p7 → False)) → False) → (((p5 ∧ p2) ∧ (False ∧ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p1 p6 p7 : Prop)
theorem file51_69779 : ((((((p1 → p6) ∨ (False → p7)) ∧ ((p1 ∧ p7) ∨ (p7 ∧ True))) → (((True → p1) ∨ (p7 ∨ True)) → ((True → False) → False))) → False) → False) := by
  intro assump_1
  have assump_224 : ((((p1 → p6) ∨ (False → p7)) ∧ ((p1 ∧ p7) ∨ (p7 ∧ True))) → (((True → p1) ∨ (p7 ∨ True)) → ((True → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              have assump_225 : True := by
                apply True.intro
              let assump_34 := assump_7 assump_225
              apply False.elim assump_34
          case inr assump_21 =>
            cases assump_21
            case intro assump_38 assump_39 =>
              have assump_226 : True := by
                apply True.intro
              let assump_48 := assump_7 assump_226
              apply False.elim assump_48
        case inr assump_17 =>
          cases assump_15
          case inl assump_54 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              have assump_227 : True := by
                apply True.intro
              let assump_67 := assump_7 assump_227
              apply False.elim assump_67
          case inr assump_55 =>
            cases assump_55
            case intro assump_71 assump_72 =>
              have assump_228 : True := by
                apply True.intro
              let assump_81 := assump_7 assump_228
              apply False.elim assump_81
    case inr assump_11 =>
      cases assump_11
      case inl assump_85 =>
        cases assump_5
        case intro assump_89 assump_90 =>
          cases assump_89
          case inl assump_91 =>
            cases assump_90
            case inl assump_95 =>
              cases assump_95
              case intro assump_97 assump_98 =>
                have assump_229 : True := by
                  apply True.intro
                let assump_108 := assump_7 assump_229
                apply False.elim assump_108
            case inr assump_96 =>
              cases assump_96
              case intro assump_112 assump_113 =>
                have assump_230 : True := by
                  apply True.intro
                let assump_121 := assump_7 assump_230
                apply False.elim assump_121
          case inr assump_92 =>
            cases assump_90
            case inl assump_127 =>
              cases assump_127
              case intro assump_129 assump_130 =>
                have assump_231 : True := by
                  apply True.intro
                let assump_139 := assump_7 assump_231
                apply False.elim assump_139
            case inr assump_128 =>
              cases assump_128
              case intro assump_143 assump_144 =>
                have assump_232 : True := by
                  apply True.intro
                let assump_152 := assump_7 assump_232
                apply False.elim assump_152
      case inr assump_86 =>
        cases assump_5
        case intro assump_158 assump_159 =>
          cases assump_158
          case inl assump_160 =>
            cases assump_159
            case inl assump_164 =>
              cases assump_164
              case intro assump_166 assump_167 =>
                have assump_233 : True := by
                  apply True.intro
                let assump_176 := assump_7 assump_233
                apply False.elim assump_176
            case inr assump_165 =>
              cases assump_165
              case intro assump_180 assump_181 =>
                have assump_234 : True := by
                  apply True.intro
                let assump_188 := assump_7 assump_234
                apply False.elim assump_188
          case inr assump_161 =>
            cases assump_159
            case inl assump_194 =>
              cases assump_194
              case intro assump_196 assump_197 =>
                have assump_235 : True := by
                  apply True.intro
                let assump_205 := assump_7 assump_235
                apply False.elim assump_205
            case inr assump_195 =>
              cases assump_195
              case intro assump_209 assump_210 =>
                have assump_236 : True := by
                  apply True.intro
                let assump_217 := assump_7 assump_236
                apply False.elim assump_217
  let assump_4 := assump_1 assump_224
  apply False.elim assump_4


variable (p3 p1 p4 p2 p0 p5 p7 : Prop)
theorem file51_74487 : ((((((True ∧ p7) ∧ (True ∧ False)) ∧ ((p1 ∨ p5) ∧ (p0 → False))) ∧ (((p3 → True) ∧ (p4 ∧ p4)) → False)) ∧ ((((False → False) ∧ (p5 ∧ p4)) → ((p2 ∨ p1) ∧ (p0 ∧ p1))) → False)) → False) := by
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
            case intro assump_16 assump_17 =>
              apply False.elim assump_17


variable (p3 p4 p6 p5 p7 p1 p2 : Prop)
theorem file51_75168 : ((((((p1 ∧ p6) → (p4 → False)) → False) ∨ (((p3 ∨ p2) → (p3 → False)) ∨ ((p7 → True) ∧ (False ∧ p4)))) ∧ ((((p6 ∧ False) → False) ∨ ((False ∧ p6) → False)) ∧ (((False → p5) → False) ∧ ((p2 → p2) ∧ (p3 ∨ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                have assump_164 : (False → p5) := by
                  intro assump_29
                  apply False.elim assump_29
                let assump_28 := assump_14 assump_164
                apply False.elim assump_28
              case inr assump_23 =>
                have assump_165 : (False → p5) := by
                  intro assump_40
                  apply False.elim assump_40
                let assump_39 := assump_14 assump_165
                apply False.elim assump_39
        case inr assump_11 =>
          cases assump_9
          case intro assump_48 assump_49 =>
            cases assump_49
            case intro assump_52 assump_53 =>
              cases assump_53
              case inl assump_56 =>
                have assump_166 : (False → p5) := by
                  intro assump_63
                  apply False.elim assump_63
                let assump_62 := assump_48 assump_166
                apply False.elim assump_62
              case inr assump_57 =>
                have assump_167 : (False → p5) := by
                  intro assump_74
                  apply False.elim assump_74
                let assump_73 := assump_48 assump_167
                apply False.elim assump_73
    case inr assump_5 =>
      cases assump_5
      case inl assump_80 =>
        cases assump_3
        case intro assump_84 assump_85 =>
          cases assump_84
          case inl assump_86 =>
            cases assump_85
            case intro assump_90 assump_91 =>
              cases assump_91
              case intro assump_94 assump_95 =>
                cases assump_95
                case inl assump_98 =>
                  have assump_168 : (False → p5) := by
                    intro assump_105
                    apply False.elim assump_105
                  let assump_104 := assump_90 assump_168
                  apply False.elim assump_104
                case inr assump_99 =>
                  have assump_169 : (False → p5) := by
                    intro assump_116
                    apply False.elim assump_116
                  let assump_115 := assump_90 assump_169
                  apply False.elim assump_115
          case inr assump_87 =>
            cases assump_85
            case intro assump_124 assump_125 =>
              cases assump_125
              case intro assump_128 assump_129 =>
                cases assump_129
                case inl assump_132 =>
                  have assump_170 : (False → p5) := by
                    intro assump_139
                    apply False.elim assump_139
                  let assump_138 := assump_124 assump_170
                  apply False.elim assump_138
                case inr assump_133 =>
                  have assump_171 : (False → p5) := by
                    intro assump_150
                    apply False.elim assump_150
                  let assump_149 := assump_124 assump_171
                  apply False.elim assump_149
      case inr assump_81 =>
        cases assump_81
        case intro assump_156 assump_157 =>
          cases assump_157
          case intro assump_160 assump_161 =>
            apply False.elim assump_160


variable (p3 p4 p6 p0 p5 : Prop)
theorem file51_79051 : (((((False ∧ False) ∧ (True → p3)) ∧ ((p6 → p4) → (p0 ∨ True))) → False) ∨ ((((p0 → False) ∨ (p6 ∨ p4)) ∧ ((p5 ∨ p6) → False)) ∧ (((True → p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p6 p4 p7 p5 p3 p1 p2 : Prop)
theorem file51_79514 : (((((p5 → False) ∧ (p6 ∧ False)) → ((p4 ∧ p4) → (p1 ∨ p2))) ∨ (((True ∨ False) → (p4 → p5)) ∧ ((p4 → False) ∨ (False → p3)))) ∨ ((((p2 → False) → (p2 ∨ p6)) → False) ∨ (((p7 → False) → (p3 → p2)) ∨ ((False → p1) ∨ (False ∧ p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply False.elim assump_14


variable (p5 p7 p0 p1 p4 : Prop)
theorem file51_80076 : (((((False → False) ∨ (p0 ∧ p0)) → False) → False) ∨ ((((False ∧ True) ∧ (p4 → False)) → ((p7 → p1) → (False ∧ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (p0 ∧ p0)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p4 p3 p0 p6 p2 p1 p7 : Prop)
theorem file51_80493 : (((((True → False) → False) → False) ∧ (((p5 ∧ p0) → (p2 → False)) ∨ ((False ∧ p6) ∧ (True ∨ p2)))) → ((((False → p7) ∨ (p1 ∨ p2)) → ((p4 ∧ p3) → False)) → (((p3 ∧ p0) ∨ (p4 → False)) ∧ ((p0 ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      apply Or.inr
      intro assump_13
      have assump_70 : ((True → False) → False) := by
        intro assump_19
        have assump_71 : True := by
          apply True.intro
        let assump_22 := assump_19 assump_71
        apply False.elim assump_22
      let assump_18 := assump_5 assump_70
      apply False.elim assump_18
    case inr assump_10 =>
      cases assump_10
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          apply False.elim assump_31
  intro assump_35
  cases assump_35
  case intro assump_36 assump_37 =>
    cases assump_1
    case intro assump_44 assump_45 =>
      cases assump_45
      case inl assump_48 =>
        have assump_72 : ((True → False) → False) := by
          intro assump_54
          have assump_73 : True := by
            apply True.intro
          let assump_57 := assump_54 assump_73
          apply False.elim assump_57
        let assump_53 := assump_44 assump_72
        apply False.elim assump_53
      case inr assump_49 =>
        cases assump_49
        case intro assump_64 assump_65 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            apply False.elim assump_66


variable (p6 p1 p3 : Prop)
theorem file51_82129 : ((((((p1 ∧ p3) → (True ∨ p6)) → ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p1 ∧ p3) → (True ∨ p6)) → ((False → False) → False)) → False) := by
    intro assump_5
    have assump_27 : ((p1 ∧ p3) → (True ∨ p6)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply True.intro
    let assump_8 := assump_5 assump_27
    have assump_28 : (False → False) := by
      intro assump_17
      apply False.elim assump_17
    let assump_16 := assump_8 assump_28
    apply False.elim assump_16
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p0 p3 p7 : Prop)
theorem file51_82856 : (((((True ∧ p5) → (p0 → False)) ∧ ((p5 ∧ p7) → (p7 ∧ p0))) ∧ (((True ∧ p5) ∧ (False → p7)) ∧ ((p3 → True) → False))) → False) := by
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
            have assump_29 : (p3 → True) := by
              intro assump_25
              apply True.intro
            let assump_24 := assump_11 assump_29
            apply False.elim assump_24


variable (p6 p2 p0 p4 p1 p3 : Prop)
theorem file51_83564 : (((((True ∧ False) → False) ∨ ((p4 ∨ p4) → False)) ∨ (((True → False) → False) ∨ ((p6 ∧ False) → (False ∨ True)))) ∨ ((((p0 → p0) → (p3 → False)) → False) → (((p0 ∧ p4) → (p4 ∨ p1)) ∧ ((p2 → False) → (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p6 p3 p5 p7 p0 p1 : Prop)
theorem file51_83990 : (((((p7 → False) → (True ∨ p7)) → False) → (((p1 → True) → False) → ((p0 → False) → False))) ∨ ((((p6 → False) ∧ (p7 → p7)) → False) ∧ (((p3 ∧ p7) → (p5 ∨ True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_17 : ((p7 → False) → (True ∨ p7)) := by
    intro assump_11
    apply Or.inl
    apply True.intro
  let assump_10 := assump_1 assump_17
  apply False.elim assump_10


variable (p3 p2 p0 p6 p4 : Prop)
theorem file51_84471 : ((((((p6 ∨ False) → False) → ((True ∨ p0) ∨ (p3 ∧ p6))) ∨ (((p2 → False) ∧ (p0 → False)) ∨ ((False ∨ p4) ∧ (p6 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 ∨ False) → False) → ((True ∨ p0) ∨ (p3 ∧ p6))) ∨ (((p2 → False) ∧ (p0 → False)) ∨ ((False ∨ p4) ∧ (p6 ∧ True)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p7 p3 p4 p6 p1 p0 : Prop)
theorem file51_84998 : (((((True ∧ p2) ∨ (False → p3)) → ((False → True) → False)) → False) ∨ ((((p0 ∧ True) ∧ (p0 ∨ p7)) ∧ ((p7 → p1) → False)) ∨ (((p1 → p4) ∧ (p6 ∨ p2)) ∨ ((True → p1) ∧ (p7 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((True ∧ p2) ∨ (False → p3)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_13
  have assump_14 : (False → True) := by
    intro assump_9
    apply True.intro
  let assump_8 := assump_4 assump_14
  apply False.elim assump_8


variable (p1 p2 p7 p3 p0 p4 : Prop)
theorem file51_85581 : (((((True ∨ p2) ∧ (p4 ∨ True)) ∨ ((True → True) → False)) ∧ (((False → False) ∨ (p0 → p0)) → False)) → ((((False → p3) → False) → ((True → False) ∨ (p3 → False))) ∧ (((p2 ∧ p2) ∧ (False ∧ p1)) ∧ ((p7 → False) ∧ (p3 ∧ p0))))) := by
  intro assump_13
  apply And.intro
  intro assump_14
  cases assump_13
  case intro assump_17 assump_18 =>
    cases assump_17
    case inl assump_19 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          cases assump_22
          case inl assump_27 =>
            apply Or.inl
            intro assump_33
            have assump_575 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_37
              apply False.elim assump_37
            let assump_36 := assump_18 assump_575
            apply False.elim assump_36
          case inr assump_28 =>
            apply Or.inl
            intro assump_47
            have assump_576 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_51
              apply False.elim assump_51
            let assump_50 := assump_18 assump_576
            apply False.elim assump_50
        case inr assump_24 =>
          cases assump_22
          case inl assump_59 =>
            apply Or.inl
            intro assump_65
            have assump_577 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_69
              apply False.elim assump_69
            let assump_68 := assump_18 assump_577
            apply False.elim assump_68
          case inr assump_60 =>
            apply Or.inl
            intro assump_79
            have assump_578 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_83
              apply False.elim assump_83
            let assump_82 := assump_18 assump_578
            apply False.elim assump_82
    case inr assump_20 =>
      apply Or.inl
      intro assump_93
      have assump_579 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_97
        apply False.elim assump_97
      let assump_96 := assump_18 assump_579
      apply False.elim assump_96
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_13
  case intro assump_103 assump_104 =>
    cases assump_103
    case inl assump_105 =>
      cases assump_105
      case intro assump_107 assump_108 =>
        cases assump_107
        case inl assump_109 =>
          cases assump_108
          case inl assump_113 =>
            have assump_580 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_120
              apply False.elim assump_120
            let assump_119 := assump_104 assump_580
            apply False.elim assump_119
          case inr assump_114 =>
            have assump_581 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_131
              apply False.elim assump_131
            let assump_130 := assump_104 assump_581
            apply False.elim assump_130
        case inr assump_110 =>
          cases assump_108
          case inl assump_139 =>
            exact assump_110
          case inr assump_140 =>
            exact assump_110
    case inr assump_106 =>
      have assump_582 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_154
        apply False.elim assump_154
      let assump_153 := assump_104 assump_582
      apply False.elim assump_153
  cases assump_13
  case intro assump_160 assump_161 =>
    cases assump_160
    case inl assump_162 =>
      cases assump_162
      case intro assump_164 assump_165 =>
        cases assump_164
        case inl assump_166 =>
          cases assump_165
          case inl assump_170 =>
            have assump_583 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_177
              apply False.elim assump_177
            let assump_176 := assump_161 assump_583
            apply False.elim assump_176
          case inr assump_171 =>
            have assump_584 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_188
              apply False.elim assump_188
            let assump_187 := assump_161 assump_584
            apply False.elim assump_187
        case inr assump_167 =>
          cases assump_165
          case inl assump_196 =>
            exact assump_167
          case inr assump_197 =>
            exact assump_167
    case inr assump_163 =>
      have assump_585 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_211
        apply False.elim assump_211
      let assump_210 := assump_161 assump_585
      apply False.elim assump_210
  apply And.intro
  cases assump_13
  case intro assump_217 assump_218 =>
    cases assump_217
    case inl assump_219 =>
      cases assump_219
      case intro assump_221 assump_222 =>
        cases assump_221
        case inl assump_223 =>
          cases assump_222
          case inl assump_227 =>
            have assump_586 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_234
              apply False.elim assump_234
            let assump_233 := assump_218 assump_586
            apply False.elim assump_233
          case inr assump_228 =>
            have assump_587 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_245
              apply False.elim assump_245
            let assump_244 := assump_218 assump_587
            apply False.elim assump_244
        case inr assump_224 =>
          cases assump_222
          case inl assump_253 =>
            have assump_588 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_260
              apply False.elim assump_260
            let assump_259 := assump_218 assump_588
            apply False.elim assump_259
          case inr assump_254 =>
            have assump_589 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_271
              apply False.elim assump_271
            let assump_270 := assump_218 assump_589
            apply False.elim assump_270
    case inr assump_220 =>
      have assump_590 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_282
        apply False.elim assump_282
      let assump_281 := assump_218 assump_590
      apply False.elim assump_281
  cases assump_13
  case intro assump_288 assump_289 =>
    cases assump_288
    case inl assump_290 =>
      cases assump_290
      case intro assump_292 assump_293 =>
        cases assump_292
        case inl assump_294 =>
          cases assump_293
          case inl assump_298 =>
            have assump_591 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_305
              apply False.elim assump_305
            let assump_304 := assump_289 assump_591
            apply False.elim assump_304
          case inr assump_299 =>
            have assump_592 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_316
              apply False.elim assump_316
            let assump_315 := assump_289 assump_592
            apply False.elim assump_315
        case inr assump_295 =>
          cases assump_293
          case inl assump_324 =>
            have assump_593 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_331
              apply False.elim assump_331
            let assump_330 := assump_289 assump_593
            apply False.elim assump_330
          case inr assump_325 =>
            have assump_594 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_342
              apply False.elim assump_342
            let assump_341 := assump_289 assump_594
            apply False.elim assump_341
    case inr assump_291 =>
      have assump_595 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_353
        apply False.elim assump_353
      let assump_352 := assump_289 assump_595
      apply False.elim assump_352
  apply And.intro
  intro assump_359
  cases assump_13
  case intro assump_362 assump_363 =>
    cases assump_362
    case inl assump_364 =>
      cases assump_364
      case intro assump_366 assump_367 =>
        cases assump_366
        case inl assump_368 =>
          cases assump_367
          case inl assump_372 =>
            have assump_596 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_379
              apply False.elim assump_379
            let assump_378 := assump_363 assump_596
            apply False.elim assump_378
          case inr assump_373 =>
            have assump_597 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_390
              apply False.elim assump_390
            let assump_389 := assump_363 assump_597
            apply False.elim assump_389
        case inr assump_369 =>
          cases assump_367
          case inl assump_398 =>
            have assump_598 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_405
              apply False.elim assump_405
            let assump_404 := assump_363 assump_598
            apply False.elim assump_404
          case inr assump_399 =>
            have assump_599 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_416
              apply False.elim assump_416
            let assump_415 := assump_363 assump_599
            apply False.elim assump_415
    case inr assump_365 =>
      have assump_600 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_427
        apply False.elim assump_427
      let assump_426 := assump_363 assump_600
      apply False.elim assump_426
  apply And.intro
  cases assump_13
  case intro assump_433 assump_434 =>
    cases assump_433
    case inl assump_435 =>
      cases assump_435
      case intro assump_437 assump_438 =>
        cases assump_437
        case inl assump_439 =>
          cases assump_438
          case inl assump_443 =>
            have assump_601 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_450
              apply False.elim assump_450
            let assump_449 := assump_434 assump_601
            apply False.elim assump_449
          case inr assump_444 =>
            have assump_602 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_461
              apply False.elim assump_461
            let assump_460 := assump_434 assump_602
            apply False.elim assump_460
        case inr assump_440 =>
          cases assump_438
          case inl assump_469 =>
            have assump_603 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_476
              apply False.elim assump_476
            let assump_475 := assump_434 assump_603
            apply False.elim assump_475
          case inr assump_470 =>
            have assump_604 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_487
              apply False.elim assump_487
            let assump_486 := assump_434 assump_604
            apply False.elim assump_486
    case inr assump_436 =>
      have assump_605 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_498
        apply False.elim assump_498
      let assump_497 := assump_434 assump_605
      apply False.elim assump_497
  cases assump_13
  case intro assump_504 assump_505 =>
    cases assump_504
    case inl assump_506 =>
      cases assump_506
      case intro assump_508 assump_509 =>
        cases assump_508
        case inl assump_510 =>
          cases assump_509
          case inl assump_514 =>
            have assump_606 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_521
              apply False.elim assump_521
            let assump_520 := assump_505 assump_606
            apply False.elim assump_520
          case inr assump_515 =>
            have assump_607 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_532
              apply False.elim assump_532
            let assump_531 := assump_505 assump_607
            apply False.elim assump_531
        case inr assump_511 =>
          cases assump_509
          case inl assump_540 =>
            have assump_608 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_547
              apply False.elim assump_547
            let assump_546 := assump_505 assump_608
            apply False.elim assump_546
          case inr assump_541 =>
            have assump_609 : ((False → False) ∨ (p0 → p0)) := by
              apply Or.inl
              intro assump_558
              apply False.elim assump_558
            let assump_557 := assump_505 assump_609
            apply False.elim assump_557
    case inr assump_507 =>
      have assump_610 : ((False → False) ∨ (p0 → p0)) := by
        apply Or.inl
        intro assump_569
        apply False.elim assump_569
      let assump_568 := assump_505 assump_610
      apply False.elim assump_568


variable (p2 p7 p6 p4 p3 p1 p5 p0 : Prop)
theorem file51_99138 : ((((((p1 ∧ p2) → (p5 ∧ p0)) ∨ ((p4 → False) ∨ (p0 → False))) ∨ (((p1 ∨ p0) → (p4 → False)) ∨ ((p6 ∨ True) ∨ (p3 → False)))) ∧ ((((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_142 : (((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) := by
          apply Or.inl
          intro assump_13
          intro assump_14
          cases assump_13
          case intro assump_17 assump_18 =>
            exact assump_17
        let assump_12 := assump_3 assump_142
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case inl assump_26 =>
          have assump_143 : (((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) := by
            apply Or.inl
            intro assump_33
            intro assump_34
            cases assump_33
            case intro assump_37 assump_38 =>
              exact assump_37
          let assump_32 := assump_3 assump_143
          apply False.elim assump_32
        case inr assump_27 =>
          have assump_144 : (((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) := by
            apply Or.inl
            intro assump_51
            intro assump_52
            cases assump_51
            case intro assump_55 assump_56 =>
              exact assump_55
          let assump_50 := assump_3 assump_144
          apply False.elim assump_50
    case inr assump_5 =>
      cases assump_5
      case inl assump_64 =>
        have assump_145 : (((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) := by
          apply Or.inl
          intro assump_71
          intro assump_72
          cases assump_71
          case intro assump_75 assump_76 =>
            exact assump_75
        let assump_70 := assump_3 assump_145
        apply False.elim assump_70
      case inr assump_65 =>
        cases assump_65
        case inl assump_84 =>
          cases assump_84
          case inl assump_86 =>
            have assump_146 : (((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) := by
              apply Or.inl
              intro assump_93
              intro assump_94
              cases assump_93
              case intro assump_97 assump_98 =>
                exact assump_97
            let assump_92 := assump_3 assump_146
            apply False.elim assump_92
          case inr assump_87 =>
            have assump_147 : (((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) := by
              apply Or.inl
              intro assump_111
              intro assump_112
              cases assump_111
              case intro assump_115 assump_116 =>
                exact assump_115
            let assump_110 := assump_3 assump_147
            apply False.elim assump_110
        case inr assump_85 =>
          have assump_148 : (((p0 ∧ p5) → (p6 → p0)) ∨ ((p7 → False) → (False ∨ p2))) := by
            apply Or.inl
            intro assump_129
            intro assump_130
            cases assump_129
            case intro assump_133 assump_134 =>
              exact assump_133
          let assump_128 := assump_3 assump_148
          apply False.elim assump_128


variable (p7 p1 p6 p5 p2 : Prop)
theorem file51_102494 : ((((((False ∨ p2) → False) → ((p1 ∨ p2) ∨ (p6 → True))) ∨ (((p1 → False) → False) → ((p7 → p5) ∨ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((False ∨ p2) → False) → ((p1 ∨ p2) ∨ (p6 → True))) ∨ (((p1 → False) → False) → ((p7 → p5) ∨ (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p2 p0 p7 p3 p1 : Prop)
theorem file51_103002 : (((((p5 ∧ p5) ∧ (p1 ∨ p0)) ∨ ((False ∧ p0) ∨ (p7 ∨ p7))) ∨ (((True → False) → (p5 ∨ p0)) ∨ ((p7 ∨ p0) → False))) ∨ ((((False → p1) → False) ∨ ((p0 → False) → (p1 ∧ p2))) ∨ (((p5 ∧ p7) → False) → ((p1 ∨ p3) ∧ (p0 → False))))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p6 p1 p3 p0 p7 p4 : Prop)
theorem file51_103472 : (((((p1 → p3) → False) ∧ ((p2 → p4) → (p1 ∧ p3))) → (((p6 ∨ p1) → (p7 → True)) ∨ ((p0 ∧ p3) ∧ (p0 ∧ p1)))) ∨ ((((p6 → p4) → False) ∨ ((True ∨ True) → False)) ∧ (((False → False) → (p7 ∨ True)) ∧ ((p3 → False) ∨ (p0 → p7))))) := by
  apply Or.inl
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply Or.inl
    intro assump_16
    intro assump_17
    apply True.intro


variable (p5 p6 p1 p0 p3 p7 : Prop)
theorem file51_103926 : (((((p1 ∨ True) → (p1 ∧ p1)) ∧ ((True → p7) → (p0 → p1))) ∧ (((False → p3) ∨ (p3 ∨ False)) → False)) → ((((p5 ∧ p0) ∨ (True ∨ p7)) → ((False ∧ p6) ∧ (p0 → False))) ∨ (((False ∧ p3) → (p5 ∨ p3)) → ((p3 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      apply And.intro
      apply And.intro
      cases assump_12
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          have assump_133 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_24
            apply False.elim assump_24
          let assump_23 := assump_3 assump_133
          apply False.elim assump_23
      case inr assump_14 =>
        cases assump_14
        case inl assump_30 =>
          have assump_134 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_35
            apply False.elim assump_35
          let assump_34 := assump_3 assump_134
          apply False.elim assump_34
        case inr assump_31 =>
          have assump_135 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_45
            apply False.elim assump_45
          let assump_44 := assump_3 assump_135
          apply False.elim assump_44
      cases assump_12
      case inl assump_51 =>
        cases assump_51
        case intro assump_53 assump_54 =>
          have assump_136 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_62
            apply False.elim assump_62
          let assump_61 := assump_3 assump_136
          apply False.elim assump_61
      case inr assump_52 =>
        cases assump_52
        case inl assump_68 =>
          have assump_137 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_73
            apply False.elim assump_73
          let assump_72 := assump_3 assump_137
          apply False.elim assump_72
        case inr assump_69 =>
          have assump_138 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_83
            apply False.elim assump_83
          let assump_82 := assump_3 assump_138
          apply False.elim assump_82
      intro assump_89
      cases assump_12
      case inl assump_92 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          have assump_139 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_104
            apply False.elim assump_104
          let assump_103 := assump_3 assump_139
          apply False.elim assump_103
      case inr assump_93 =>
        cases assump_93
        case inl assump_110 =>
          have assump_140 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_116
            apply False.elim assump_116
          let assump_115 := assump_3 assump_140
          apply False.elim assump_115
        case inr assump_111 =>
          have assump_141 : ((False → p3) ∨ (p3 ∨ False)) := by
            apply Or.inl
            intro assump_127
            apply False.elim assump_127
          let assump_126 := assump_3 assump_141
          apply False.elim assump_126


variable (p4 p0 p2 p1 p7 : Prop)
theorem file51_107299 : (((((p4 ∨ True) ∨ (p1 → False)) ∧ ((p7 → p4) ∨ (p1 ∨ p0))) ∧ (((False → False) ∨ (p1 ∧ p2)) → False)) → False) := by
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
          case inl assump_12 =>
            have assump_127 : ((False → False) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_19
              apply False.elim assump_19
            let assump_18 := assump_3 assump_127
            apply False.elim assump_18
          case inr assump_13 =>
            cases assump_13
            case inl assump_25 =>
              have assump_128 : ((False → False) ∨ (p1 ∧ p2)) := by
                apply Or.inl
                intro assump_32
                apply False.elim assump_32
              let assump_31 := assump_3 assump_128
              apply False.elim assump_31
            case inr assump_26 =>
              have assump_129 : ((False → False) ∨ (p1 ∧ p2)) := by
                apply Or.inl
                intro assump_43
                apply False.elim assump_43
              let assump_42 := assump_3 assump_129
              apply False.elim assump_42
        case inr assump_9 =>
          cases assump_5
          case inl assump_51 =>
            have assump_130 : ((False → False) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_58
              apply False.elim assump_58
            let assump_57 := assump_3 assump_130
            apply False.elim assump_57
          case inr assump_52 =>
            cases assump_52
            case inl assump_64 =>
              have assump_131 : ((False → False) ∨ (p1 ∧ p2)) := by
                apply Or.inl
                intro assump_71
                apply False.elim assump_71
              let assump_70 := assump_3 assump_131
              apply False.elim assump_70
            case inr assump_65 =>
              have assump_132 : ((False → False) ∨ (p1 ∧ p2)) := by
                apply Or.inl
                intro assump_82
                apply False.elim assump_82
              let assump_81 := assump_3 assump_132
              apply False.elim assump_81
      case inr assump_7 =>
        cases assump_5
        case inl assump_90 =>
          have assump_133 : ((False → False) ∨ (p1 ∧ p2)) := by
            apply Or.inl
            intro assump_97
            apply False.elim assump_97
          let assump_96 := assump_3 assump_133
          apply False.elim assump_96
        case inr assump_91 =>
          cases assump_91
          case inl assump_103 =>
            have assump_134 : ((False → False) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_110
              apply False.elim assump_110
            let assump_109 := assump_3 assump_134
            apply False.elim assump_109
          case inr assump_104 =>
            have assump_135 : ((False → False) ∨ (p1 ∧ p2)) := by
              apply Or.inl
              intro assump_121
              apply False.elim assump_121
            let assump_120 := assump_3 assump_135
            apply False.elim assump_120


variable (p0 p4 p6 p3 p2 p7 p1 : Prop)
theorem file51_110615 : (((((p0 ∧ True) ∨ (p4 → p1)) → ((p2 ∧ False) → (p0 ∧ False))) → False) → ((((True ∨ p3) ∧ (p2 ∧ False)) ∨ ((p0 ∨ p7) ∨ (p6 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          apply False.elim assump_12
      case inr assump_8 =>
        cases assump_6
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
  case inr assump_4 =>
    cases assump_4
    case inl assump_25 =>
      cases assump_25
      case inl assump_27 =>
        have assump_95 : (((p0 ∧ True) ∨ (p4 → p1)) → ((p2 ∧ False) → (p0 ∧ False))) := by
          intro assump_34
          intro assump_35
          apply And.intro
          cases assump_35
          case intro assump_36 assump_37 =>
            apply False.elim assump_37
          cases assump_35
          case intro assump_42 assump_43 =>
            apply False.elim assump_43
        let assump_33 := assump_1 assump_95
        apply False.elim assump_33
      case inr assump_28 =>
        have assump_96 : (((p0 ∧ True) ∨ (p4 → p1)) → ((p2 ∧ False) → (p0 ∧ False))) := by
          intro assump_56
          intro assump_57
          apply And.intro
          cases assump_57
          case intro assump_58 assump_59 =>
            apply False.elim assump_59
          cases assump_57
          case intro assump_64 assump_65 =>
            apply False.elim assump_65
        let assump_55 := assump_1 assump_96
        apply False.elim assump_55
    case inr assump_26 =>
      have assump_97 : (((p0 ∧ True) ∨ (p4 → p1)) → ((p2 ∧ False) → (p0 ∧ False))) := by
        intro assump_78
        intro assump_79
        apply And.intro
        cases assump_79
        case intro assump_80 assump_81 =>
          apply False.elim assump_81
        cases assump_79
        case intro assump_86 assump_87 =>
          apply False.elim assump_87
      let assump_77 := assump_1 assump_97
      apply False.elim assump_77


variable (p5 p4 p6 p0 p2 p7 p3 : Prop)
theorem file51_112782 : (((((p7 → False) ∧ (True → False)) ∨ ((p2 → p3) ∧ (p4 ∨ True))) ∧ (((p3 ∨ p5) → False) → False)) → ((((True ∨ False) → False) → ((p0 ∨ p4) → (p2 → p6))) ∨ (((True ∧ p7) ∧ (p5 ∨ True)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        intro assump_14
        intro assump_15
        intro assump_16
        cases assump_15
        case inl assump_19 =>
          have assump_97 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_25 := assump_14 assump_97
          apply False.elim assump_25
        case inr assump_20 =>
          have assump_98 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_33 := assump_14 assump_98
          apply False.elim assump_33
    case inr assump_5 =>
      cases assump_5
      case intro assump_37 assump_38 =>
        cases assump_38
        case inl assump_41 =>
          apply Or.inl
          intro assump_47
          intro assump_48
          intro assump_49
          cases assump_48
          case inl assump_52 =>
            have assump_99 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_58 := assump_47 assump_99
            apply False.elim assump_58
          case inr assump_53 =>
            have assump_100 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_66 := assump_47 assump_100
            apply False.elim assump_66
        case inr assump_42 =>
          apply Or.inl
          intro assump_74
          intro assump_75
          intro assump_76
          cases assump_75
          case inl assump_79 =>
            have assump_101 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_85 := assump_74 assump_101
            apply False.elim assump_85
          case inr assump_80 =>
            have assump_102 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_93 := assump_74 assump_102
            apply False.elim assump_93


variable (p2 p3 p4 p7 p6 p1 p5 p0 : Prop)
theorem file51_115111 : (((((p5 ∧ p2) → (p4 ∨ p2)) → False) → (((False → p2) ∧ (p0 → False)) ∨ ((p0 → False) ∨ (p7 → p7)))) ∨ ((((p3 → p4) → (True ∨ p5)) → ((p6 → False) ∧ (p5 → False))) → (((p0 ∨ p0) → False) → ((p1 ∨ p7) ∧ (p4 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  have assump_22 : ((p5 ∧ p2) → (p4 ∨ p2)) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply Or.inr
      exact assump_14
  let assump_11 := assump_1 assump_22
  apply False.elim assump_11


variable (p1 p4 p7 p3 p2 p5 p6 p0 : Prop)
theorem file51_115760 : (((((p6 → p3) ∨ (p4 ∨ True)) → False) ∧ (((p1 → False) ∧ (p0 ∧ False)) ∧ ((p4 ∨ p7) ∨ (p6 ∨ p1)))) → ((((p2 → p2) → (p5 → p1)) ∧ ((p3 ∧ p1) → (p5 → True))) ∧ (((False ∧ True) → (p3 → p7)) ∨ ((p7 → False) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          apply False.elim assump_19
  intro assump_24
  intro assump_25
  apply True.intro
  cases assump_1
  case intro assump_26 assump_27 =>
    cases assump_27
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_33
        case intro assump_36 assump_37 =>
          apply False.elim assump_37


variable (p7 p3 p2 p1 p4 p6 p0 : Prop)
theorem file51_116736 : ((((((p4 ∧ p0) ∧ (p0 ∨ p4)) ∨ ((p2 ∧ p6) ∨ (p4 → False))) ∧ (((False ∨ p7) → (p0 ∨ p0)) ∨ ((p7 ∧ True) → (p2 → False)))) ∧ ((((p1 ∧ p0) → (p3 → p3)) → ((p6 → False) → False)) ∧ (((p2 → False) → (False → False)) → False))) → False) := by
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
              cases assump_5
              case inl assump_20 =>
                cases assump_3
                case intro assump_24 assump_25 =>
                  have assump_168 : ((p2 → False) → (False → False)) := by
                    intro assump_31
                    intro assump_32
                    apply False.elim assump_32
                  let assump_30 := assump_25 assump_168
                  apply False.elim assump_30
              case inr assump_21 =>
                cases assump_3
                case intro assump_40 assump_41 =>
                  have assump_169 : ((p2 → False) → (False → False)) := by
                    intro assump_47
                    intro assump_48
                    apply False.elim assump_48
                  let assump_46 := assump_41 assump_169
                  apply False.elim assump_46
            case inr assump_17 =>
              cases assump_5
              case inl assump_56 =>
                cases assump_3
                case intro assump_60 assump_61 =>
                  have assump_170 : ((p2 → False) → (False → False)) := by
                    intro assump_67
                    intro assump_68
                    apply False.elim assump_68
                  let assump_66 := assump_61 assump_170
                  apply False.elim assump_66
              case inr assump_57 =>
                cases assump_3
                case intro assump_76 assump_77 =>
                  have assump_171 : ((p2 → False) → (False → False)) := by
                    intro assump_83
                    intro assump_84
                    apply False.elim assump_84
                  let assump_82 := assump_77 assump_171
                  apply False.elim assump_82
      case inr assump_7 =>
        cases assump_7
        case inl assump_90 =>
          cases assump_90
          case intro assump_92 assump_93 =>
            cases assump_5
            case inl assump_98 =>
              cases assump_3
              case intro assump_102 assump_103 =>
                have assump_172 : ((p2 → False) → (False → False)) := by
                  intro assump_109
                  intro assump_110
                  apply False.elim assump_110
                let assump_108 := assump_103 assump_172
                apply False.elim assump_108
            case inr assump_99 =>
              cases assump_3
              case intro assump_118 assump_119 =>
                have assump_173 : ((p2 → False) → (False → False)) := by
                  intro assump_125
                  intro assump_126
                  apply False.elim assump_126
                let assump_124 := assump_119 assump_173
                apply False.elim assump_124
        case inr assump_91 =>
          cases assump_5
          case inl assump_134 =>
            cases assump_3
            case intro assump_138 assump_139 =>
              have assump_174 : ((p2 → False) → (False → False)) := by
                intro assump_145
                intro assump_146
                apply False.elim assump_146
              let assump_144 := assump_139 assump_174
              apply False.elim assump_144
          case inr assump_135 =>
            cases assump_3
            case intro assump_154 assump_155 =>
              have assump_175 : ((p2 → False) → (False → False)) := by
                intro assump_161
                intro assump_162
                apply False.elim assump_162
              let assump_160 := assump_155 assump_175
              apply False.elim assump_160


variable (p2 p4 p6 p1 p0 p7 : Prop)
theorem file51_120943 : (((((p4 ∨ p6) → False) → False) ∧ (((p7 ∨ False) ∧ (p7 → False)) ∧ ((p6 ∧ p0) ∧ (p1 ∨ p0)))) → ((((p0 ∧ p0) ∧ (p6 → p2)) → False) ∧ (((p2 ∨ p0) → (p2 ∧ True)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_18
              case intro assump_27 assump_28 =>
                cases assump_27
                case intro assump_29 assump_30 =>
                  cases assump_28
                  case inl assump_35 =>
                    have assump_104 : p7 := by
                      exact assump_21
                    let assump_42 := assump_20 assump_104
                    apply False.elim assump_42
                  case inr assump_36 =>
                    have assump_105 : p7 := by
                      exact assump_21
                    let assump_51 := assump_20 assump_105
                    apply False.elim assump_51
            case inr assump_22 =>
              apply False.elim assump_22
  intro assump_57
  cases assump_1
  case intro assump_60 assump_61 =>
    cases assump_61
    case intro assump_64 assump_65 =>
      cases assump_64
      case intro assump_66 assump_67 =>
        cases assump_66
        case inl assump_68 =>
          cases assump_65
          case intro assump_74 assump_75 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              cases assump_75
              case inl assump_82 =>
                have assump_106 : p7 := by
                  exact assump_68
                let assump_89 := assump_67 assump_106
                apply False.elim assump_89
              case inr assump_83 =>
                have assump_107 : p7 := by
                  exact assump_68
                let assump_98 := assump_67 assump_107
                apply False.elim assump_98
        case inr assump_69 =>
          apply False.elim assump_69


variable (p2 p6 p1 : Prop)
theorem file51_123222 : ((((((False ∨ p2) ∨ (p2 → p6)) → False) → (((p2 → p1) → False) → False)) → False) → False) := by
  intro assump_5
  have assump_30 : ((((False ∨ p2) ∨ (p2 → p6)) → False) → (((p2 → p1) → False) → False)) := by
    intro assump_9
    intro assump_10
    have assump_31 : ((False ∨ p2) ∨ (p2 → p6)) := by
      apply Or.inr
      intro assump_16
      have assump_32 : ((False ∨ p2) ∨ (p2 → p6)) := by
        apply Or.inl
        apply Or.inr
        exact assump_16
      let assump_20 := assump_9 assump_32
      apply False.elim assump_20
    let assump_15 := assump_9 assump_31
    apply False.elim assump_15
  let assump_8 := assump_5 assump_30
  apply False.elim assump_8


variable (p0 p5 p3 p4 p6 p7 : Prop)
theorem file51_123959 : (((((p5 → True) → False) → False) ∧ (((True → False) ∧ (p6 ∧ p6)) ∧ ((p3 ∧ p0) ∧ (p7 → p4)))) → ((((p4 ∧ p4) → False) ∨ ((False ∧ p5) ∨ (p5 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            cases assump_12
            case intro assump_23 assump_24 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                have assump_85 : True := by
                  apply True.intro
                let assump_38 := assump_13 assump_85
                apply False.elim assump_38
  case inr assump_4 =>
    cases assump_4
    case inl assump_42 =>
      cases assump_42
      case intro assump_44 assump_45 =>
        apply False.elim assump_44
    case inr assump_43 =>
      cases assump_1
      case intro assump_50 assump_51 =>
        cases assump_51
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            cases assump_57
            case intro assump_60 assump_61 =>
              cases assump_55
              case intro assump_66 assump_67 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  have assump_86 : True := by
                    apply True.intro
                  let assump_81 := assump_56 assump_86
                  apply False.elim assump_81


variable (p7 p4 p5 p6 p1 p0 p3 p2 : Prop)
theorem file51_125650 : (((((p2 ∧ p2) → False) → False) → (((True → p3) ∧ (p1 ∨ p3)) → ((p3 → p7) → False))) → ((((False ∨ False) → (p6 → False)) ∨ ((p6 ∨ True) ∨ (p0 → False))) ∨ (((True → False) ∨ (p6 → p4)) → ((p6 ∨ p5) ∨ (p6 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    apply False.elim assump_8
  case inr assump_9 =>
    apply False.elim assump_9


variable (p3 p0 p5 p4 p1 p7 : Prop)
theorem file51_126138 : (((((False ∧ p1) ∧ (p3 → p4)) ∧ ((p3 → False) → False)) → (((False ∨ False) ∨ (False → p0)) ∨ ((p7 ∨ p7) → False))) ∨ ((((p1 → p5) → False) → False) ∧ (((p7 → False) ∨ (p0 → p4)) → ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p1 p2 p5 p4 p7 : Prop)
theorem file51_126639 : ((((((p4 ∧ p7) → False) ∨ ((p2 → False) ∨ (p1 ∨ p5))) → False) ∧ ((((p7 ∨ p5) ∧ (False ∧ p5)) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_33 : (((p7 ∨ p5) ∧ (False ∧ p5)) → False) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
        case inr assump_17 =>
          cases assump_15
          case intro assump_26 assump_27 =>
            apply False.elim assump_26
    let assump_12 := assump_7 assump_33
    apply False.elim assump_12


variable (p7 p4 p0 p5 p2 p1 p6 : Prop)
theorem file51_127419 : ((((((p7 → False) → False) ∨ ((p0 ∧ p0) → (p6 → p2))) ∨ (((p5 ∨ False) → (p7 ∧ p1)) → False)) ∧ ((((p5 ∨ p4) ∧ (p1 → True)) ∨ ((p0 ∧ p2) → (p5 → False))) ∧ (((p0 → p0) → False) ∧ ((True ∨ p7) → False)))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_22
              case inl assump_24 =>
                cases assump_19
                case intro assump_30 assump_31 =>
                  have assump_166 : (True ∨ p7) := by
                    apply Or.inl
                    apply True.intro
                  let assump_36 := assump_31 assump_166
                  apply False.elim assump_36
              case inr assump_25 =>
                cases assump_19
                case intro assump_44 assump_45 =>
                  have assump_167 : (True ∨ p7) := by
                    apply Or.inl
                    apply True.intro
                  let assump_50 := assump_45 assump_167
                  apply False.elim assump_50
          case inr assump_21 =>
            cases assump_19
            case intro assump_56 assump_57 =>
              have assump_168 : (True ∨ p7) := by
                apply Or.inl
                apply True.intro
              let assump_62 := assump_57 assump_168
              apply False.elim assump_62
      case inr assump_15 =>
        cases assump_11
        case intro assump_68 assump_69 =>
          cases assump_68
          case inl assump_70 =>
            cases assump_70
            case intro assump_72 assump_73 =>
              cases assump_72
              case inl assump_74 =>
                cases assump_69
                case intro assump_80 assump_81 =>
                  have assump_169 : (True ∨ p7) := by
                    apply Or.inl
                    apply True.intro
                  let assump_86 := assump_81 assump_169
                  apply False.elim assump_86
              case inr assump_75 =>
                cases assump_69
                case intro assump_94 assump_95 =>
                  have assump_170 : (True ∨ p7) := by
                    apply Or.inl
                    apply True.intro
                  let assump_100 := assump_95 assump_170
                  apply False.elim assump_100
          case inr assump_71 =>
            cases assump_69
            case intro assump_106 assump_107 =>
              have assump_171 : (True ∨ p7) := by
                apply Or.inl
                apply True.intro
              let assump_112 := assump_107 assump_171
              apply False.elim assump_112
    case inr assump_13 =>
      cases assump_11
      case intro assump_118 assump_119 =>
        cases assump_118
        case inl assump_120 =>
          cases assump_120
          case intro assump_122 assump_123 =>
            cases assump_122
            case inl assump_124 =>
              cases assump_119
              case intro assump_130 assump_131 =>
                have assump_172 : (True ∨ p7) := by
                  apply Or.inl
                  apply True.intro
                let assump_136 := assump_131 assump_172
                apply False.elim assump_136
            case inr assump_125 =>
              cases assump_119
              case intro assump_144 assump_145 =>
                have assump_173 : (True ∨ p7) := by
                  apply Or.inl
                  apply True.intro
                let assump_150 := assump_145 assump_173
                apply False.elim assump_150
        case inr assump_121 =>
          cases assump_119
          case intro assump_156 assump_157 =>
            have assump_174 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_162 := assump_157 assump_174
            apply False.elim assump_162


variable (p7 p4 p3 p5 p0 : Prop)
theorem file51_131564 : ((((((p7 → p0) → (True → p0)) → ((False ∧ p0) → False)) ∨ (((p4 ∧ p5) → False) ∧ ((p3 → p3) → (p5 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p7 → p0) → (True → p0)) → ((False ∧ p0) → False)) ∨ (((p4 ∧ p5) → False) ∧ ((p3 → p3) → (p5 ∧ True)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p6 p4 p2 p1 p7 : Prop)
theorem file51_132113 : ((((((True ∧ p4) → False) → False) → (((p6 ∨ p7) → (p4 → p1)) ∧ ((p4 → p7) → (p2 ∧ False)))) ∧ ((((p7 → False) → False) ∧ ((p7 ∧ p7) ∨ (p7 → False))) ∧ (((p2 → p5) ∨ (True → False)) ∧ ((p2 ∨ p7) → False)))) → False) := by
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
              cases assump_20
              case inl assump_22 =>
                have assump_74 : (p2 ∨ p7) := by
                  apply Or.inr
                  exact assump_15
                let assump_28 := assump_21 assump_74
                apply False.elim assump_28
              case inr assump_23 =>
                have assump_75 : (p2 ∨ p7) := by
                  apply Or.inr
                  exact assump_15
                let assump_36 := assump_21 assump_75
                apply False.elim assump_36
        case inr assump_13 =>
          cases assump_7
          case intro assump_42 assump_43 =>
            cases assump_42
            case inl assump_44 =>
              have assump_76 : (p7 → False) := by
                intro assump_54
                have assump_77 : (p2 ∨ p7) := by
                  apply Or.inr
                  exact assump_54
                let assump_58 := assump_43 assump_77
                apply False.elim assump_58
              let assump_53 := assump_8 assump_76
              apply False.elim assump_53
            case inr assump_45 =>
              have assump_78 : True := by
                apply True.intro
              let assump_70 := assump_45 assump_78
              apply False.elim assump_70


variable (p1 p5 p3 p0 p4 : Prop)
theorem file51_134037 : ((((((False → False) ∧ (p0 ∨ p0)) ∨ ((p5 ∧ p5) ∨ (p5 → False))) ∨ (((True ∨ p5) → (p3 ∨ p4)) ∨ ((False → False) ∨ (p1 → False)))) → False) → False) := by
  intro assump_5
  have assump_26 : ((((False → False) ∧ (p0 ∨ p0)) ∨ ((p5 ∧ p5) ∨ (p5 → False))) ∨ (((True ∨ p5) → (p3 ∨ p4)) ∨ ((False → False) ∨ (p1 → False)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_12
    have assump_27 : ((((False → False) ∧ (p0 ∨ p0)) ∨ ((p5 ∧ p5) ∨ (p5 → False))) ∨ (((True ∨ p5) → (p3 ∨ p4)) ∨ ((False → False) ∨ (p1 → False)))) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply And.intro
      exact assump_12
      exact assump_12
    let assump_16 := assump_5 assump_27
    apply False.elim assump_16
  let assump_8 := assump_5 assump_26
  apply False.elim assump_8


variable (p7 p2 p0 p1 p5 p4 p6 : Prop)
theorem file51_134909 : ((((((p7 → False) → (p2 → p2)) ∧ ((False ∨ p0) ∧ (p2 ∧ True))) ∧ (((p0 ∧ p4) → (p5 ∧ p0)) ∨ ((p7 → False) ∧ (p6 → p2)))) ∧ ((((p1 → p0) → (False → False)) → ((True → p2) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              cases assump_5
              case inl assump_24 =>
                have assump_58 : (((p1 → p0) → (False → False)) → ((True → p2) ∨ (False → False))) := by
                  intro assump_31
                  apply Or.inl
                  intro assump_34
                  exact assump_18
                let assump_30 := assump_3 assump_58
                apply False.elim assump_30
              case inr assump_25 =>
                cases assump_25
                case intro assump_40 assump_41 =>
                  have assump_59 : (((p1 → p0) → (False → False)) → ((True → p2) ∨ (False → False))) := by
                    intro assump_49
                    apply Or.inl
                    intro assump_52
                    exact assump_18
                  let assump_48 := assump_3 assump_59
                  apply False.elim assump_48


variable (p1 p4 p2 p0 p3 p5 p7 : Prop)
theorem file51_136500 : (((((p2 → p0) → (p1 → False)) ∧ ((p5 → False) → False)) → (((p4 → False) → (p1 ∨ p3)) → False)) → ((((p1 ∨ p5) → False) → False) → (((p2 ∧ p1) → False) → ((p2 → p2) ∨ (p7 → False))))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  apply Or.inl
  intro assump_14
  exact assump_14


variable (p7 p4 p0 p3 p5 : Prop)
theorem file51_136849 : ((((((p7 → False) ∧ (p7 → False)) ∧ ((p4 ∨ p0) → (p0 ∧ p4))) ∧ (((p5 ∧ False) → (p3 → False)) ∨ ((p3 → False) → (p4 ∧ p5)))) ∧ ((((p5 → False) → (True ∨ p4)) ∨ ((False → False) ∨ (p4 ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case inl assump_16 =>
            have assump_40 : (((p5 → False) → (True ∨ p4)) ∨ ((False → False) ∨ (p4 ∨ p5))) := by
              apply Or.inl
              intro assump_23
              apply Or.inl
              apply True.intro
            let assump_22 := assump_3 assump_40
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_41 : (((p5 → False) → (True ∨ p4)) ∨ ((False → False) ∨ (p4 ∨ p5))) := by
              apply Or.inl
              intro assump_34
              apply Or.inl
              apply True.intro
            let assump_33 := assump_3 assump_41
            apply False.elim assump_33


variable (p1 p6 p7 p4 p2 p5 p3 : Prop)
theorem file51_138062 : ((((((p3 ∧ p2) ∨ (p2 ∨ p6)) → ((False → False) → (p1 → p1))) → (((p4 → False) → (p5 → True)) ∨ ((p6 ∧ p4) ∧ (p3 → p7)))) → False) → False) := by
  intro assump_10
  have assump_22 : ((((p3 ∧ p2) ∨ (p2 ∨ p6)) → ((False → False) → (p1 → p1))) → (((p4 → False) → (p5 → True)) ∨ ((p6 ∧ p4) ∧ (p3 → p7)))) := by
    intro assump_14
    apply Or.inl
    intro assump_17
    intro assump_18
    apply True.intro
  let assump_13 := assump_10 assump_22
  apply False.elim assump_13


variable (p6 p2 p0 p3 p1 : Prop)
theorem file51_138592 : ((((((True → False) → (p0 ∨ True)) ∧ ((p2 ∧ p0) ∧ (True → False))) → (((p0 ∨ p6) ∨ (p1 → False)) ∨ ((False ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((True → False) → (p0 ∨ True)) ∧ ((p2 ∧ p0) ∧ (True → False))) → (((p0 ∨ p6) ∨ (p1 → False)) ∨ ((False ∧ p3) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_13
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p6 p0 p2 p7 p4 : Prop)
theorem file51_139325 : (((((p4 ∧ False) ∧ (p2 → False)) ∧ ((p6 → False) → (p3 ∧ p0))) ∧ (((p4 ∧ True) → (p2 ∧ True)) → ((p0 ∧ p7) → (p6 ∧ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9


variable (p5 p2 p1 p0 p7 : Prop)
theorem file51_139800 : ((((((True → True) → False) → False) ∨ (((p2 → False) ∧ (p0 → p5)) ∧ ((True ∧ p7) → (p1 → True)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((True → True) → False) → False) ∨ (((p2 → False) ∧ (p0 → p5)) ∧ ((True ∧ p7) → (p1 → True)))) := by
    apply Or.inl
    intro assump_5
    have assump_17 : (True → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p7 p6 p1 p5 p2 : Prop)
theorem file51_140377 : (((((p5 ∧ False) ∨ (p6 ∨ p1)) ∨ ((p3 → False) ∨ (True → False))) → (((p3 → True) → False) → ((p5 → False) ∨ (p5 ∨ p2)))) ∨ ((((True ∧ p5) → False) ∧ ((p1 ∧ p2) → False)) → (((False → False) ∨ (p7 ∧ p5)) ∨ ((p7 ∧ p1) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      cases assump_8
      case inl assump_15 =>
        apply Or.inl
        intro assump_19
        have assump_65 : (p3 → True) := by
          intro assump_25
          apply True.intro
        let assump_24 := assump_2 assump_65
        apply False.elim assump_24
      case inr assump_16 =>
        apply Or.inl
        intro assump_31
        have assump_66 : (p3 → True) := by
          intro assump_37
          apply True.intro
        let assump_36 := assump_2 assump_66
        apply False.elim assump_36
  case inr assump_6 =>
    cases assump_6
    case inl assump_41 =>
      apply Or.inl
      intro assump_45
      have assump_67 : (p3 → True) := by
        intro assump_51
        apply True.intro
      let assump_50 := assump_2 assump_67
      apply False.elim assump_50
    case inr assump_42 =>
      apply Or.inl
      intro assump_57
      have assump_68 : True := by
        apply True.intro
      let assump_61 := assump_42 assump_68
      apply False.elim assump_61


variable (p3 p1 p4 p6 p0 p2 : Prop)
theorem file51_141917 : ((((((p4 → p2) ∨ (p1 ∨ False)) ∨ ((p4 ∧ p6) ∨ (p1 ∨ p3))) → False) ∧ ((((p0 ∧ p6) ∧ (False ∧ False)) → False) → False)) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    have assump_39 : (((p0 ∧ p6) ∧ (False ∧ False)) → False) := by
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_25
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
    let assump_22 := assump_17 assump_39
    apply False.elim assump_22


variable (p4 p5 p6 p3 : Prop)
theorem file51_142576 : ((((((p3 → p3) → False) ∧ ((p3 → p4) → False)) → (((p5 ∧ True) ∧ (False → False)) ∨ ((p6 ∧ p4) → False))) → False) → False) := by
  intro assump_12
  have assump_42 : ((((p3 → p3) → False) ∧ ((p3 → p4) → False)) → (((p5 ∧ True) ∧ (False → False)) ∨ ((p6 ∧ p4) → False))) := by
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply Or.inr
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        have assump_43 : (p3 → p4) := by
          intro assump_33
          exact assump_25
        let assump_32 := assump_18 assump_43
        apply False.elim assump_32
  let assump_15 := assump_12 assump_42
  apply False.elim assump_15


variable (p0 p4 p1 p5 p2 : Prop)
theorem file51_143332 : ((((((p1 ∧ p0) → False) ∨ ((True → p2) ∨ (False → p2))) → False) ∧ ((((False ∨ p1) → False) ∧ ((p1 → False) ∨ (p5 ∧ p0))) ∧ (((False ∨ p4) ∧ (p2 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_71 : (((p1 ∧ p0) → False) ∨ ((True → p2) ∨ (False → p2))) := by
            apply Or.inl
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              have assump_72 : p1 := by
                exact assump_23
              let assump_32 := assump_12 assump_72
              apply False.elim assump_32
          let assump_21 := assump_2 assump_71
          apply False.elim assump_21
        case inr assump_13 =>
          cases assump_13
          case intro assump_39 assump_40 =>
            have assump_73 : (((p1 ∧ p0) → False) ∨ ((True → p2) ∨ (False → p2))) := by
              apply Or.inl
              intro assump_52
              cases assump_52
              case intro assump_53 assump_54 =>
                have assump_74 : (False ∨ p1) := by
                  apply Or.inr
                  exact assump_53
                let assump_64 := assump_8 assump_74
                apply False.elim assump_64
            let assump_51 := assump_2 assump_73
            apply False.elim assump_51


variable (p1 p0 p7 p2 : Prop)
theorem file51_144884 : (((((False → False) → False) ∧ ((False → False) → False)) → (((False → p1) → False) ∧ ((p7 → False) → (p0 ∧ False)))) ∨ ((((p1 ∧ p0) ∧ (p2 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_49 : (False → False) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_6 assump_49
    apply False.elim assump_11
  intro assump_18
  apply And.intro
  cases assump_1
  case intro assump_21 assump_22 =>
    have assump_50 : (False → False) := by
      intro assump_28
      apply False.elim assump_28
    let assump_27 := assump_22 assump_50
    apply False.elim assump_27
  cases assump_1
  case intro assump_36 assump_37 =>
    have assump_51 : (False → False) := by
      intro assump_43
      apply False.elim assump_43
    let assump_42 := assump_37 assump_51
    apply False.elim assump_42


variable (p7 p6 p2 p1 p4 p0 p3 : Prop)
theorem file51_145890 : (((((p0 → p4) → False) → ((False ∨ p1) → (False → p3))) → False) → ((((p7 → p7) ∨ (True ∧ False)) ∧ ((p4 ∨ False) → False)) ∧ (((p6 ∧ p1) ∧ (p6 → p2)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  exact assump_4
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    have assump_47 : (((p0 → p4) → False) → ((False ∨ p1) → (False → p3))) := by
      intro assump_15
      intro assump_16
      intro assump_17
      apply False.elim assump_17
    let assump_14 := assump_1 assump_47
    apply False.elim assump_14
  case inr assump_9 =>
    apply False.elim assump_9
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    cases assump_26
    case intro assump_28 assump_29 =>
      have assump_48 : (((p0 → p4) → False) → ((False ∨ p1) → (False → p3))) := by
        intro assump_39
        intro assump_40
        intro assump_41
        apply False.elim assump_41
      let assump_38 := assump_1 assump_48
      apply False.elim assump_38


variable (p7 p2 p0 p1 p4 p6 : Prop)
theorem file51_146976 : ((((((p4 ∨ p2) → False) → ((p6 → p7) → (p0 → False))) → (((p4 → p6) ∨ (p1 → False)) → False)) ∧ ((((p2 → p4) → (p6 → p2)) → ((p1 → False) → (p2 → True))) → (((True ∧ p2) ∨ (p0 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p2 → p4) → (p6 → p2)) → ((p1 → False) → (p2 → True))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_17
    have assump_18 : ((True ∧ p2) ∨ (p0 → True)) := by
      apply Or.inr
      intro assump_13
      apply True.intro
    let assump_12 := assump_8 assump_18
    apply False.elim assump_12


variable (p5 p3 p4 p0 p7 p1 : Prop)
theorem file51_147716 : ((((((p1 ∨ p5) → (p7 → True)) → ((p3 → False) ∨ (p3 ∨ False))) → False) ∧ ((((p5 → p1) → False) ∧ ((p4 → False) ∧ (False ∧ p1))) ∧ (((p5 → False) → False) → ((p1 ∧ p3) ∨ (True ∨ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply False.elim assump_16


variable (p0 p3 p7 p5 p4 p2 : Prop)
theorem file51_148333 : (((((p0 → p0) → False) → ((p0 → False) ∧ (p5 → False))) ∨ (((p3 ∨ p4) → False) ∧ ((False ∧ p2) → False))) ∨ ((((p0 ∨ p0) → False) → False) ∨ (((p5 ∨ p0) ∨ (p4 ∧ p2)) → ((p2 → p4) ∨ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_11
  apply And.intro
  intro assump_12
  have assump_36 : (p0 → p0) := by
    intro assump_18
    exact assump_18
  let assump_17 := assump_11 assump_36
  apply False.elim assump_17
  intro assump_24
  have assump_37 : (p0 → p0) := by
    intro assump_30
    exact assump_30
  let assump_29 := assump_11 assump_37
  apply False.elim assump_29


variable (p6 p5 p4 p0 p3 : Prop)
theorem file51_148982 : ((((((p4 → False) → False) → ((p4 ∧ p6) ∨ (p5 → False))) → (((p6 → True) ∨ (p3 → False)) ∨ ((p0 → False) ∨ (False ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p4 → False) → False) → ((p4 ∧ p6) ∨ (p5 → False))) → (((p6 → True) ∨ (p3 → False)) ∨ ((p0 → False) ∨ (False ∨ p0)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p1 p3 p0 p6 : Prop)
theorem file51_149507 : ((((((p0 ∨ p6) → (p5 ∧ p5)) → ((p5 ∧ p1) ∨ (p6 ∧ p3))) ∧ (((True → False) → False) ∧ ((p5 ∧ p5) ∨ (p6 → False)))) ∧ ((((False → False) → False) → ((False ∧ False) ∨ (p1 → p3))) → False)) → False) := by
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
          case intro assump_14 assump_15 =>
            have assump_62 : (((False → False) → False) → ((False ∧ False) ∨ (p1 → p3))) := by
              intro assump_23
              apply Or.inr
              intro assump_26
              have assump_63 : (False → False) := by
                intro assump_31
                apply False.elim assump_31
              let assump_30 := assump_23 assump_63
              apply False.elim assump_30
            let assump_22 := assump_3 assump_62
            apply False.elim assump_22
        case inr assump_13 =>
          have assump_64 : (((False → False) → False) → ((False ∧ False) ∨ (p1 → p3))) := by
            intro assump_45
            apply Or.inr
            intro assump_48
            have assump_65 : (False → False) := by
              intro assump_53
              apply False.elim assump_53
            let assump_52 := assump_45 assump_65
            apply False.elim assump_52
          let assump_44 := assump_3 assump_64
          apply False.elim assump_44


variable (p6 p2 p1 p4 p7 : Prop)
theorem file51_151057 : (((((False ∨ p2) → False) → ((False ∧ p4) → (p1 ∨ p7))) → False) → ((((p1 ∨ p2) ∨ (p6 ∨ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_17 : (((False ∨ p2) → False) → ((False ∧ p4) → (p1 ∨ p7))) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_7 := assump_1 assump_17
  apply False.elim assump_7


variable (p0 p3 p6 p5 : Prop)
theorem file51_151535 : ((((((p5 → p3) → (p3 ∨ p6)) ∧ ((p5 ∧ False) ∧ (p0 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p5 → p3) → (p3 ∨ p6)) ∧ ((p5 ∧ False) ∧ (p0 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p4 p0 p2 p1 p6 p5 : Prop)
theorem file51_152105 : ((((((False ∨ False) ∧ (p2 ∧ False)) ∧ ((True → False) ∨ (p1 → p7))) ∧ (((p4 → p0) → False) ∨ ((p6 ∧ p6) → (p7 → False)))) ∧ ((((p1 → p0) ∨ (p5 → True)) ∧ ((p5 → False) → (p7 → False))) → False)) → False) := by
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
          case inl assump_10 =>
            apply False.elim assump_10
          case inr assump_11 =>
            apply False.elim assump_11


variable (p6 p3 p7 p1 p5 p2 : Prop)
theorem file51_152788 : ((((((p1 ∨ False) → False) ∧ ((p1 ∧ p7) ∧ (True ∧ p5))) → (((False → False) ∨ (p6 → False)) → False)) ∧ ((((p3 ∧ p2) ∧ (p5 → False)) → ((p1 → True) ∨ (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p3 ∧ p2) ∧ (p5 → False)) → ((p1 → True) ∨ (p5 → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          apply True.intro
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p6 p0 : Prop)
theorem file51_153474 : (((((True → False) → (p0 → False)) ∧ ((p6 ∨ p0) ∨ (False → True))) → False) → False) := by
  intro assump_1
  have assump_19 : (((True → False) → (p0 → False)) ∧ ((p6 ∨ p0) ∨ (False → True))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    have assump_20 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_20
    apply False.elim assump_11
    apply Or.inr
    intro assump_15
    apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p0 p4 p5 p7 p2 : Prop)
theorem file51_154039 : (((((p0 ∧ p7) → False) ∧ ((p3 ∧ p4) ∨ (p7 → False))) ∧ (((False ∧ p5) → (p7 → False)) ∧ ((p0 ∨ p3) ∧ (p2 ∨ p3)))) → ((((False → False) ∧ (p2 ∨ False)) ∧ ((False → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_18
            case inl assump_21 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                cases assump_16
                case intro assump_29 assump_30 =>
                  cases assump_30
                  case intro assump_33 assump_34 =>
                    cases assump_33
                    case inl assump_35 =>
                      cases assump_34
                      case inl assump_39 =>
                        have assump_181 : (False → False) := by
                          intro assump_50
                          apply False.elim assump_50
                        let assump_49 := assump_4 assump_181
                        apply False.elim assump_49
                      case inr assump_40 =>
                        have assump_182 : (False → False) := by
                          intro assump_65
                          apply False.elim assump_65
                        let assump_64 := assump_4 assump_182
                        apply False.elim assump_64
                    case inr assump_36 =>
                      cases assump_34
                      case inl assump_73 =>
                        have assump_183 : (False → False) := by
                          intro assump_84
                          apply False.elim assump_84
                        let assump_83 := assump_4 assump_183
                        apply False.elim assump_83
                      case inr assump_74 =>
                        have assump_184 : (False → False) := by
                          intro assump_99
                          apply False.elim assump_99
                        let assump_98 := assump_4 assump_184
                        apply False.elim assump_98
            case inr assump_22 =>
              cases assump_16
              case intro assump_107 assump_108 =>
                cases assump_108
                case intro assump_111 assump_112 =>
                  cases assump_111
                  case inl assump_113 =>
                    cases assump_112
                    case inl assump_117 =>
                      have assump_185 : (False → False) := by
                        intro assump_127
                        apply False.elim assump_127
                      let assump_126 := assump_4 assump_185
                      apply False.elim assump_126
                    case inr assump_118 =>
                      have assump_186 : (False → False) := by
                        intro assump_141
                        apply False.elim assump_141
                      let assump_140 := assump_4 assump_186
                      apply False.elim assump_140
                  case inr assump_114 =>
                    cases assump_112
                    case inl assump_149 =>
                      have assump_187 : (False → False) := by
                        intro assump_159
                        apply False.elim assump_159
                      let assump_158 := assump_4 assump_187
                      apply False.elim assump_158
                    case inr assump_150 =>
                      have assump_188 : (False → False) := by
                        intro assump_173
                        apply False.elim assump_173
                      let assump_172 := assump_4 assump_188
                      apply False.elim assump_172
      case inr assump_10 =>
        apply False.elim assump_10


