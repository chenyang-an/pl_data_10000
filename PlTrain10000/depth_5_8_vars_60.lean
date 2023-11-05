variable (p2 p6 p1 p3 p0 p7 p4 : Prop)
theorem file60_47 : ((((((p6 ∧ p0) ∧ (False ∨ p0)) ∧ ((False → p7) ∧ (p4 ∧ False))) ∧ (((True ∧ True) → (p1 ∧ p0)) → ((p3 ∧ False) ∧ (p7 ∧ p1)))) ∧ ((((True → False) → (p2 → p6)) ∧ ((True → False) ∧ (False → False))) → (((p3 ∧ p0) ∨ (p2 ∧ p2)) → False))) → False) := by
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
              apply False.elim assump_16
            case inr assump_17 =>
              cases assump_7
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  apply False.elim assump_27


variable (p1 p7 p4 p3 p5 p0 : Prop)
theorem file60_1011 : (((((False ∧ p0) ∨ (p1 → False)) → ((p1 ∧ p5) ∧ (p4 → False))) ∧ (((p7 ∨ p0) → (p3 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_14 : ((p7 ∨ p0) → (p3 → True)) := by
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_3 assump_14
    apply False.elim assump_8


variable (p7 p6 p5 p0 p2 : Prop)
theorem file60_1441 : (((((True → False) → (p0 ∨ p2)) → False) → (((False ∨ False) → False) → False)) ∨ ((((p5 → False) ∨ (p6 ∧ p7)) ∨ ((True → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_18 : ((True → False) → (p0 ∨ p2)) := by
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_7 := assump_1 assump_18
  apply False.elim assump_7


variable (p6 p5 p3 p0 p4 p1 : Prop)
theorem file60_1969 : (((((p1 ∨ p0) ∧ (p3 ∨ p5)) → False) ∧ (((p6 ∨ p0) → False) ∧ ((p5 ∨ p5) → False))) → ((((True ∨ p0) ∨ (True → p6)) ∨ ((p4 ∨ True) ∨ (p0 → p3))) ∨ (((p1 ∨ p1) → False) → False))) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_22
    case intro assump_25 assump_26 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p5 p2 p0 p3 p7 : Prop)
theorem file60_2439 : (((((p3 → p7) ∨ (p5 → False)) → ((False ∧ p0) ∧ (p5 → False))) → False) → ((((p7 ∧ True) ∨ (False → False)) ∨ ((True → p7) → False)) ∧ (((p3 ∨ True) ∨ (True ∧ p2)) → ((False ∧ p3) → (p5 ∧ p7))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  intro assump_8
  apply And.intro
  cases assump_8
  case intro assump_9 assump_10 =>
    apply False.elim assump_9
  cases assump_8
  case intro assump_13 assump_14 =>
    apply False.elim assump_13


variable (p5 p1 p6 p7 : Prop)
theorem file60_3023 : (((((p7 ∨ p7) ∧ (p5 → False)) → False) ∧ (((p1 ∨ True) ∨ (p7 → p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((p1 ∨ True) ∨ (p7 → p6)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p5 p4 p7 p0 p1 p6 : Prop)
theorem file60_3427 : (((((p6 → False) ∧ (p7 → False)) → False) → False) → ((((False → False) → (p5 → False)) ∨ ((p6 → False) ∧ (p0 ∧ p4))) → (((p0 → p7) ∧ (p7 → True)) → ((p1 → False) → (p7 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_3
  case intro assump_10 assump_11 =>
    cases assump_2
    case inl assump_16 =>
      have assump_64 : (((p6 → False) ∧ (p7 → False)) → False) := by
        intro assump_23
        cases assump_23
        case intro assump_24 assump_25 =>
          have assump_65 : p7 := by
            exact assump_5
          let assump_30 := assump_25 assump_65
          apply False.elim assump_30
      let assump_22 := assump_1 assump_64
      apply False.elim assump_22
    case inr assump_17 =>
      cases assump_17
      case intro assump_37 assump_38 =>
        cases assump_38
        case intro assump_41 assump_42 =>
          have assump_66 : (((p6 → False) ∧ (p7 → False)) → False) := by
            intro assump_50
            cases assump_50
            case intro assump_51 assump_52 =>
              have assump_67 : p7 := by
                exact assump_5
              let assump_57 := assump_52 assump_67
              apply False.elim assump_57
          let assump_49 := assump_1 assump_66
          apply False.elim assump_49


variable (p5 p4 p7 p1 p2 p6 p0 : Prop)
theorem file60_4817 : ((((((p5 → False) → (p6 → False)) ∨ ((p5 ∨ False) ∨ (p6 ∨ True))) ∧ (((p4 → p0) ∧ (p0 ∧ p4)) → False)) ∧ ((((p0 → False) → (p0 → p7)) → False) ∧ (((p6 ∧ p2) → (False ∨ False)) ∨ ((p2 → False) ∨ (p2 ∨ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            have assump_344 : ((p0 → False) → (p0 → p7)) := by
              intro assump_22
              intro assump_23
              have assump_345 : p0 := by
                exact assump_23
              let assump_28 := assump_22 assump_345
              apply False.elim assump_28
            let assump_21 := assump_12 assump_344
            apply False.elim assump_21
          case inr assump_17 =>
            cases assump_17
            case inl assump_35 =>
              have assump_346 : ((p0 → False) → (p0 → p7)) := by
                intro assump_41
                intro assump_42
                have assump_347 : p0 := by
                  exact assump_42
                let assump_47 := assump_41 assump_347
                apply False.elim assump_47
              let assump_40 := assump_12 assump_346
              apply False.elim assump_40
            case inr assump_36 =>
              cases assump_36
              case inl assump_54 =>
                have assump_348 : ((p0 → False) → (p0 → p7)) := by
                  intro assump_60
                  intro assump_61
                  have assump_349 : p0 := by
                    exact assump_61
                  let assump_66 := assump_60 assump_349
                  apply False.elim assump_66
                let assump_59 := assump_12 assump_348
                apply False.elim assump_59
              case inr assump_55 =>
                have assump_350 : ((p0 → False) → (p0 → p7)) := by
                  intro assump_77
                  intro assump_78
                  have assump_351 : p0 := by
                    exact assump_78
                  let assump_83 := assump_77 assump_351
                  apply False.elim assump_83
                let assump_76 := assump_12 assump_350
                apply False.elim assump_76
      case inr assump_7 =>
        cases assump_7
        case inl assump_90 =>
          cases assump_90
          case inl assump_92 =>
            cases assump_3
            case intro assump_98 assump_99 =>
              cases assump_99
              case inl assump_102 =>
                have assump_352 : ((p0 → False) → (p0 → p7)) := by
                  intro assump_108
                  intro assump_109
                  have assump_353 : p0 := by
                    exact assump_109
                  let assump_114 := assump_108 assump_353
                  apply False.elim assump_114
                let assump_107 := assump_98 assump_352
                apply False.elim assump_107
              case inr assump_103 =>
                cases assump_103
                case inl assump_121 =>
                  have assump_354 : ((p0 → False) → (p0 → p7)) := by
                    intro assump_127
                    intro assump_128
                    have assump_355 : p0 := by
                      exact assump_128
                    let assump_133 := assump_127 assump_355
                    apply False.elim assump_133
                  let assump_126 := assump_98 assump_354
                  apply False.elim assump_126
                case inr assump_122 =>
                  cases assump_122
                  case inl assump_140 =>
                    have assump_356 : ((p0 → False) → (p0 → p7)) := by
                      intro assump_146
                      intro assump_147
                      have assump_357 : p0 := by
                        exact assump_147
                      let assump_152 := assump_146 assump_357
                      apply False.elim assump_152
                    let assump_145 := assump_98 assump_356
                    apply False.elim assump_145
                  case inr assump_141 =>
                    have assump_358 : ((p0 → False) → (p0 → p7)) := by
                      intro assump_163
                      intro assump_164
                      have assump_359 : p0 := by
                        exact assump_164
                      let assump_169 := assump_163 assump_359
                      apply False.elim assump_169
                    let assump_162 := assump_98 assump_358
                    apply False.elim assump_162
          case inr assump_93 =>
            apply False.elim assump_93
        case inr assump_91 =>
          cases assump_91
          case inl assump_178 =>
            cases assump_3
            case intro assump_184 assump_185 =>
              cases assump_185
              case inl assump_188 =>
                have assump_360 : ((p0 → False) → (p0 → p7)) := by
                  intro assump_194
                  intro assump_195
                  have assump_361 : p0 := by
                    exact assump_195
                  let assump_200 := assump_194 assump_361
                  apply False.elim assump_200
                let assump_193 := assump_184 assump_360
                apply False.elim assump_193
              case inr assump_189 =>
                cases assump_189
                case inl assump_207 =>
                  have assump_362 : ((p0 → False) → (p0 → p7)) := by
                    intro assump_213
                    intro assump_214
                    have assump_363 : p0 := by
                      exact assump_214
                    let assump_219 := assump_213 assump_363
                    apply False.elim assump_219
                  let assump_212 := assump_184 assump_362
                  apply False.elim assump_212
                case inr assump_208 =>
                  cases assump_208
                  case inl assump_226 =>
                    have assump_364 : ((p0 → False) → (p0 → p7)) := by
                      intro assump_232
                      intro assump_233
                      have assump_365 : p0 := by
                        exact assump_233
                      let assump_238 := assump_232 assump_365
                      apply False.elim assump_238
                    let assump_231 := assump_184 assump_364
                    apply False.elim assump_231
                  case inr assump_227 =>
                    have assump_366 : ((p0 → False) → (p0 → p7)) := by
                      intro assump_249
                      intro assump_250
                      have assump_367 : p0 := by
                        exact assump_250
                      let assump_255 := assump_249 assump_367
                      apply False.elim assump_255
                    let assump_248 := assump_184 assump_366
                    apply False.elim assump_248
          case inr assump_179 =>
            cases assump_3
            case intro assump_266 assump_267 =>
              cases assump_267
              case inl assump_270 =>
                have assump_368 : ((p0 → False) → (p0 → p7)) := by
                  intro assump_276
                  intro assump_277
                  have assump_369 : p0 := by
                    exact assump_277
                  let assump_282 := assump_276 assump_369
                  apply False.elim assump_282
                let assump_275 := assump_266 assump_368
                apply False.elim assump_275
              case inr assump_271 =>
                cases assump_271
                case inl assump_289 =>
                  have assump_370 : ((p0 → False) → (p0 → p7)) := by
                    intro assump_295
                    intro assump_296
                    have assump_371 : p0 := by
                      exact assump_296
                    let assump_301 := assump_295 assump_371
                    apply False.elim assump_301
                  let assump_294 := assump_266 assump_370
                  apply False.elim assump_294
                case inr assump_290 =>
                  cases assump_290
                  case inl assump_308 =>
                    have assump_372 : ((p0 → False) → (p0 → p7)) := by
                      intro assump_314
                      intro assump_315
                      have assump_373 : p0 := by
                        exact assump_315
                      let assump_320 := assump_314 assump_373
                      apply False.elim assump_320
                    let assump_313 := assump_266 assump_372
                    apply False.elim assump_313
                  case inr assump_309 =>
                    have assump_374 : ((p0 → False) → (p0 → p7)) := by
                      intro assump_331
                      intro assump_332
                      have assump_375 : p0 := by
                        exact assump_332
                      let assump_337 := assump_331 assump_375
                      apply False.elim assump_337
                    let assump_330 := assump_266 assump_374
                    apply False.elim assump_330


variable (p7 p1 p6 p2 p5 p3 : Prop)
theorem file60_14120 : ((((((True → False) ∧ (False → p3)) → ((p6 ∧ p5) → (p1 ∨ p1))) ∨ (((False ∨ True) → False) ∧ ((True → False) ∧ (p2 → False)))) → ((((p5 ∧ p3) ∧ (p7 ∨ p7)) ∨ ((p1 ∨ p5) → (False → p2))) → False)) → False) := by
  intro assump_1
  have assump_32 : ((((True → False) ∧ (False → p3)) → ((p6 ∧ p5) → (p1 ∨ p1))) ∨ (((False ∨ True) → False) ∧ ((True → False) ∧ (p2 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        have assump_33 : True := by
          apply True.intro
        let assump_20 := assump_13 assump_33
        apply False.elim assump_20
  let assump_4 := assump_1 assump_32
  have assump_34 : (((p5 ∧ p3) ∧ (p7 ∨ p7)) ∨ ((p1 ∨ p5) → (False → p2))) := by
    apply Or.inr
    intro assump_25
    intro assump_26
    apply False.elim assump_26
  let assump_24 := assump_4 assump_34
  apply False.elim assump_24


variable (p4 p7 p3 p5 p6 p2 : Prop)
theorem file60_15143 : (((((p6 ∧ p7) → False) ∨ ((p4 → False) ∧ (False ∧ p7))) → False) → ((((p3 → p5) → False) ∧ ((True ∨ False) → (False ∧ True))) → (((p2 ∧ p4) ∧ (True ∧ p7)) ∨ ((True → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inr
    intro assump_11
    have assump_18 : True := by
      apply True.intro
    let assump_14 := assump_11 assump_18
    apply False.elim assump_14


variable (p5 p7 p0 p4 p2 p6 p3 : Prop)
theorem file60_15646 : (((((p7 → False) ∧ (p6 ∧ False)) → False) → False) → ((((True → False) ∨ (p5 ∨ p3)) ∨ ((p7 → False) → (p4 ∧ p0))) → (((True ∨ p2) → (p4 ∧ p6)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      intro assump_11
      apply And.intro
      cases assump_11
      case inl assump_12 =>
        have assump_325 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
          intro assump_17
          cases assump_17
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              apply False.elim assump_23
        let assump_16 := assump_1 assump_325
        apply False.elim assump_16
      case inr assump_13 =>
        have assump_326 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
          intro assump_35
          cases assump_35
          case intro assump_36 assump_37 =>
            cases assump_37
            case intro assump_40 assump_41 =>
              apply False.elim assump_41
        let assump_34 := assump_1 assump_326
        apply False.elim assump_34
      cases assump_11
      case inl assump_49 =>
        have assump_327 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
          intro assump_54
          cases assump_54
          case intro assump_55 assump_56 =>
            cases assump_56
            case intro assump_59 assump_60 =>
              apply False.elim assump_60
        let assump_53 := assump_1 assump_327
        apply False.elim assump_53
      case inr assump_50 =>
        have assump_328 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
          intro assump_72
          cases assump_72
          case intro assump_73 assump_74 =>
            cases assump_74
            case intro assump_77 assump_78 =>
              apply False.elim assump_78
        let assump_71 := assump_1 assump_328
        apply False.elim assump_71
    case inr assump_6 =>
      cases assump_6
      case inl assump_86 =>
        apply Or.inl
        intro assump_92
        apply And.intro
        cases assump_92
        case inl assump_93 =>
          have assump_329 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_98
            cases assump_98
            case intro assump_99 assump_100 =>
              cases assump_100
              case intro assump_103 assump_104 =>
                apply False.elim assump_104
          let assump_97 := assump_1 assump_329
          apply False.elim assump_97
        case inr assump_94 =>
          have assump_330 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_116
            cases assump_116
            case intro assump_117 assump_118 =>
              cases assump_118
              case intro assump_121 assump_122 =>
                apply False.elim assump_122
          let assump_115 := assump_1 assump_330
          apply False.elim assump_115
        cases assump_92
        case inl assump_130 =>
          have assump_331 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_135
            cases assump_135
            case intro assump_136 assump_137 =>
              cases assump_137
              case intro assump_140 assump_141 =>
                apply False.elim assump_141
          let assump_134 := assump_1 assump_331
          apply False.elim assump_134
        case inr assump_131 =>
          have assump_332 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_153
            cases assump_153
            case intro assump_154 assump_155 =>
              cases assump_155
              case intro assump_158 assump_159 =>
                apply False.elim assump_159
          let assump_152 := assump_1 assump_332
          apply False.elim assump_152
      case inr assump_87 =>
        apply Or.inl
        intro assump_171
        apply And.intro
        cases assump_171
        case inl assump_172 =>
          have assump_333 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_177
            cases assump_177
            case intro assump_178 assump_179 =>
              cases assump_179
              case intro assump_182 assump_183 =>
                apply False.elim assump_183
          let assump_176 := assump_1 assump_333
          apply False.elim assump_176
        case inr assump_173 =>
          have assump_334 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_195
            cases assump_195
            case intro assump_196 assump_197 =>
              cases assump_197
              case intro assump_200 assump_201 =>
                apply False.elim assump_201
          let assump_194 := assump_1 assump_334
          apply False.elim assump_194
        cases assump_171
        case inl assump_209 =>
          have assump_335 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_214
            cases assump_214
            case intro assump_215 assump_216 =>
              cases assump_216
              case intro assump_219 assump_220 =>
                apply False.elim assump_220
          let assump_213 := assump_1 assump_335
          apply False.elim assump_213
        case inr assump_210 =>
          have assump_336 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
            intro assump_232
            cases assump_232
            case intro assump_233 assump_234 =>
              cases assump_234
              case intro assump_237 assump_238 =>
                apply False.elim assump_238
          let assump_231 := assump_1 assump_336
          apply False.elim assump_231
  case inr assump_4 =>
    apply Or.inl
    intro assump_250
    apply And.intro
    cases assump_250
    case inl assump_251 =>
      have assump_337 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
        intro assump_256
        cases assump_256
        case intro assump_257 assump_258 =>
          cases assump_258
          case intro assump_261 assump_262 =>
            apply False.elim assump_262
      let assump_255 := assump_1 assump_337
      apply False.elim assump_255
    case inr assump_252 =>
      have assump_338 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
        intro assump_274
        cases assump_274
        case intro assump_275 assump_276 =>
          cases assump_276
          case intro assump_279 assump_280 =>
            apply False.elim assump_280
      let assump_273 := assump_1 assump_338
      apply False.elim assump_273
    cases assump_250
    case inl assump_288 =>
      have assump_339 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
        intro assump_293
        cases assump_293
        case intro assump_294 assump_295 =>
          cases assump_295
          case intro assump_298 assump_299 =>
            apply False.elim assump_299
      let assump_292 := assump_1 assump_339
      apply False.elim assump_292
    case inr assump_289 =>
      have assump_340 : (((p7 → False) ∧ (p6 ∧ False)) → False) := by
        intro assump_311
        cases assump_311
        case intro assump_312 assump_313 =>
          cases assump_313
          case intro assump_316 assump_317 =>
            apply False.elim assump_317
      let assump_310 := assump_1 assump_340
      apply False.elim assump_310


variable (p5 p1 p6 p2 p3 p4 p0 : Prop)
theorem file60_23034 : (((((False → p3) ∧ (True ∨ p6)) ∧ ((True ∨ p4) → False)) → False) ∨ ((((p6 ∧ p5) → (True ∨ p1)) ∧ ((p2 ∨ p0) ∧ (p0 ∨ p5))) → (((p5 ∨ True) → (True ∧ True)) → ((p1 ∨ p5) ∧ (p3 → p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_26 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_14 := assump_3 assump_26
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_27 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_22 := assump_3 assump_27
        apply False.elim assump_22


variable (p4 p0 p1 p3 p7 p6 p2 : Prop)
theorem file60_23845 : (((((p3 ∧ p7) ∨ (p7 → False)) → False) → (((p0 → False) ∧ (p1 → False)) ∨ ((p0 ∧ p2) → (p2 ∨ p7)))) → ((((p4 ∨ p6) ∧ (p7 ∨ p6)) → ((False ∧ False) → (p1 → False))) ∨ (((p4 ∨ p1) → (p0 → p3)) → ((p0 → p7) ∧ (p7 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    apply False.elim assump_9


variable (p0 p4 p3 p5 p1 p6 : Prop)
theorem file60_24299 : ((((((p5 → p3) → False) ∨ ((p4 → False) → False)) ∧ (((p6 ∨ p4) → False) → ((p0 → False) → False))) ∧ ((((p6 ∧ p1) → (p1 ∨ True)) ∨ ((p6 → p5) → (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_42 : (((p6 ∧ p1) → (p1 ∨ True)) ∨ ((p6 → p5) → (p3 → False))) := by
          apply Or.inl
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply Or.inl
            exact assump_17
        let assump_14 := assump_3 assump_42
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_43 : (((p6 ∧ p1) → (p1 ∨ True)) ∨ ((p6 → p5) → (p3 → False))) := by
          apply Or.inl
          intro assump_32
          cases assump_32
          case intro assump_33 assump_34 =>
            apply Or.inl
            exact assump_34
        let assump_31 := assump_3 assump_43
        apply False.elim assump_31


variable (p0 p7 p2 p5 p4 p1 p6 : Prop)
theorem file60_25423 : ((((((p6 ∨ True) → False) → ((p7 → p6) ∨ (p0 ∧ p2))) ∨ (((p4 → False) ∨ (True ∧ p1)) → ((p5 → False) ∨ (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 ∨ True) → False) → ((p7 → p6) ∨ (p0 ∧ p2))) ∨ (((p4 → False) ∨ (True ∧ p1)) → ((p5 → False) ∨ (p4 → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_20 : (p6 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p5 p2 p0 p6 p3 p7 : Prop)
theorem file60_26077 : (((((p6 ∧ True) ∧ (p3 → p1)) ∧ ((p2 ∧ p6) → (p3 → p0))) → (((p6 ∧ True) ∨ (p7 → False)) → ((True ∧ p7) ∨ (p7 ∧ p2)))) → ((((p7 → False) → (p0 → False)) → False) → (((p5 → p0) → (False → p7)) ∨ ((False → p5) → (p6 ∧ p5))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  apply False.elim assump_8


variable (p7 p4 p5 p3 p1 p0 p6 : Prop)
theorem file60_26480 : (((((True → False) → (True ∧ p6)) → False) → (((True → p6) → False) ∧ ((p5 → p0) ∧ (p7 → False)))) ∨ ((((p1 → False) → False) ∨ ((False → False) ∨ (True → False))) → (((p4 ∧ p0) ∨ (p1 → False)) → ((p3 → False) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_50 : ((True → False) → (True ∧ p6)) := by
    intro assump_8
    apply And.intro
    apply True.intro
    have assump_51 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_51
    apply False.elim assump_11
  let assump_7 := assump_1 assump_50
  apply False.elim assump_7
  apply And.intro
  intro assump_18
  have assump_52 : ((True → False) → (True ∧ p6)) := by
    intro assump_24
    apply And.intro
    apply True.intro
    have assump_53 : True := by
      apply True.intro
    let assump_27 := assump_24 assump_53
    apply False.elim assump_27
  let assump_23 := assump_1 assump_52
  apply False.elim assump_23
  intro assump_34
  have assump_54 : ((True → False) → (True ∧ p6)) := by
    intro assump_40
    apply And.intro
    apply True.intro
    have assump_55 : True := by
      apply True.intro
    let assump_43 := assump_40 assump_55
    apply False.elim assump_43
  let assump_39 := assump_1 assump_54
  apply False.elim assump_39


variable (p0 p5 p7 p2 p4 p6 p3 : Prop)
theorem file60_27828 : ((((((p3 ∧ False) → (p5 ∨ p0)) → False) ∧ (((p5 → p7) → (p6 → p2)) ∧ ((p6 ∧ p7) ∧ (False → False)))) ∧ ((((p4 ∨ p2) → (p5 → False)) ∨ ((p6 → p6) → False)) ∧ (((p6 → p0) → (p6 ∨ p0)) → ((True → False) ∧ (True → False))))) → False) := by
  intro assump_39
  cases assump_39
  case intro assump_40 assump_41 =>
    cases assump_40
    case intro assump_42 assump_43 =>
      cases assump_43
      case intro assump_46 assump_47 =>
        cases assump_47
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            cases assump_41
            case intro assump_60 assump_61 =>
              cases assump_60
              case inl assump_62 =>
                have assump_90 : ((p6 → p0) → (p6 ∨ p0)) := by
                  intro assump_69
                  apply Or.inl
                  exact assump_52
                let assump_68 := assump_61 assump_90
                let assump_72 := And.left assump_68
                have assump_91 : True := by
                  apply True.intro
                let assump_73 := assump_72 assump_91
                apply False.elim assump_73
              case inr assump_63 =>
                have assump_92 : ((p6 → p0) → (p6 ∨ p0)) := by
                  intro assump_82
                  apply Or.inl
                  exact assump_52
                let assump_81 := assump_61 assump_92
                let assump_85 := And.left assump_81
                have assump_93 : True := by
                  apply True.intro
                let assump_86 := assump_85 assump_93
                apply False.elim assump_86


variable (p5 p0 p2 p1 p6 p3 p4 : Prop)
theorem file60_29515 : (((((False → p2) ∧ (p1 → p6)) ∨ ((p1 → False) ∨ (p4 ∧ p6))) ∧ (((p0 → p0) → (True ∨ p6)) ∨ ((p4 → p0) → False))) → ((((False → False) ∨ (p2 → p3)) ∨ ((p3 → False) → False)) ∨ (((True ∧ False) ∧ (p4 ∨ p5)) → ((p2 ∨ p6) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case inl assump_12 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_16
          apply False.elim assump_16
        case inr assump_13 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
    case inr assump_5 =>
      cases assump_5
      case inl assump_24 =>
        cases assump_3
        case inl assump_28 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_32
          apply False.elim assump_32
        case inr assump_29 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_37
          apply False.elim assump_37
      case inr assump_25 =>
        cases assump_25
        case intro assump_40 assump_41 =>
          cases assump_3
          case inl assump_46 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            intro assump_50
            apply False.elim assump_50
          case inr assump_47 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            intro assump_55
            apply False.elim assump_55


variable (p5 p6 p2 p0 p7 p3 : Prop)
theorem file60_31217 : ((((((p5 ∧ p7) ∨ (p3 ∧ p0)) ∨ ((p0 ∧ p0) → False)) → (((p6 → False) ∧ (p7 → False)) → ((True ∨ False) → (p6 → False)))) → ((((p6 → p5) → False) → ((p3 ∧ p7) → (False → p2))) → (((False ∧ True) ∧ (p2 ∧ p2)) ∧ ((p7 → p0) → False)))) → False) := by
  intro assump_5
  have assump_76 : ((((p5 ∧ p7) ∨ (p3 ∧ p0)) ∨ ((p0 ∧ p0) → False)) → (((p6 → False) ∧ (p7 → False)) → ((True ∨ False) → (p6 → False)))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    intro assump_12
    cases assump_11
    case inl assump_15 =>
      cases assump_10
      case intro assump_19 assump_20 =>
        cases assump_9
        case inl assump_25 =>
          cases assump_25
          case inl assump_27 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              have assump_77 : p7 := by
                exact assump_30
              let assump_37 := assump_20 assump_77
              apply False.elim assump_37
          case inr assump_28 =>
            cases assump_28
            case intro assump_41 assump_42 =>
              have assump_78 : p6 := by
                exact assump_12
              let assump_50 := assump_19 assump_78
              apply False.elim assump_50
        case inr assump_26 =>
          have assump_79 : p6 := by
            exact assump_12
          let assump_58 := assump_19 assump_79
          apply False.elim assump_58
    case inr assump_16 =>
      apply False.elim assump_16
  let assump_8 := assump_5 assump_76
  have assump_80 : (((p6 → p5) → False) → ((p3 ∧ p7) → (False → p2))) := by
    intro assump_65
    intro assump_66
    intro assump_67
    apply False.elim assump_67
  let assump_64 := assump_8 assump_80
  let assump_70 := And.left assump_64
  let assump_71 := And.left assump_70
  let assump_72 := And.left assump_71
  apply False.elim assump_72


variable (p3 p5 p7 p2 p1 p6 p4 : Prop)
theorem file60_33114 : (((((p7 ∨ p3) ∨ (p3 ∨ True)) → ((p1 ∨ p5) ∨ (p2 → p2))) → False) → ((((p5 → False) → False) ∧ ((False → False) ∧ (p4 → p4))) ∧ (((p6 ∨ p3) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_82 : (((p7 ∨ p3) ∨ (p3 ∨ True)) → ((p1 ∨ p5) ∨ (p2 → p2))) := by
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inr
        intro assump_15
        exact assump_15
      case inr assump_12 =>
        apply Or.inr
        intro assump_20
        exact assump_20
    case inr assump_10 =>
      cases assump_10
      case inl assump_23 =>
        apply Or.inr
        intro assump_27
        exact assump_27
      case inr assump_24 =>
        apply Or.inr
        intro assump_32
        exact assump_32
  let assump_7 := assump_1 assump_82
  apply False.elim assump_7
  apply And.intro
  intro assump_38
  apply False.elim assump_38
  intro assump_41
  exact assump_41
  intro assump_46
  have assump_83 : (((p7 ∨ p3) ∨ (p3 ∨ True)) → ((p1 ∨ p5) ∨ (p2 → p2))) := by
    intro assump_52
    cases assump_52
    case inl assump_53 =>
      cases assump_53
      case inl assump_55 =>
        apply Or.inr
        intro assump_59
        exact assump_59
      case inr assump_56 =>
        apply Or.inr
        intro assump_64
        exact assump_64
    case inr assump_54 =>
      cases assump_54
      case inl assump_67 =>
        apply Or.inr
        intro assump_71
        exact assump_71
      case inr assump_68 =>
        apply Or.inr
        intro assump_76
        exact assump_76
  let assump_51 := assump_1 assump_83
  apply False.elim assump_51


variable (p1 p6 p7 p5 p4 : Prop)
theorem file60_34859 : (((((p6 → False) ∧ (True → False)) ∨ ((p6 ∨ p5) → False)) → (((False → p4) ∧ (p1 ∨ p4)) → ((p4 ∧ p6) → (True → False)))) ∧ ((((False → p7) ∨ (p5 → False)) → False) → False)) := by
  apply And.intro
  intro assump_119
  intro assump_120
  intro assump_121
  intro assump_122
  cases assump_121
  case intro assump_125 assump_126 =>
    cases assump_120
    case intro assump_131 assump_132 =>
      cases assump_132
      case inl assump_135 =>
        cases assump_119
        case inl assump_139 =>
          cases assump_139
          case intro assump_141 assump_142 =>
            have assump_187 : True := by
              apply True.intro
            let assump_147 := assump_142 assump_187
            apply False.elim assump_147
        case inr assump_140 =>
          have assump_188 : (p6 ∨ p5) := by
            apply Or.inl
            exact assump_126
          let assump_153 := assump_140 assump_188
          apply False.elim assump_153
      case inr assump_136 =>
        cases assump_119
        case inl assump_159 =>
          cases assump_159
          case intro assump_161 assump_162 =>
            have assump_189 : True := by
              apply True.intro
            let assump_167 := assump_162 assump_189
            apply False.elim assump_167
        case inr assump_160 =>
          have assump_190 : (p6 ∨ p5) := by
            apply Or.inl
            exact assump_126
          let assump_173 := assump_160 assump_190
          apply False.elim assump_173
  intro assump_177
  have assump_191 : ((False → p7) ∨ (p5 → False)) := by
    apply Or.inl
    intro assump_181
    apply False.elim assump_181
  let assump_180 := assump_177 assump_191
  apply False.elim assump_180


variable (p4 p3 p2 p7 p0 p6 p1 p5 : Prop)
theorem file60_36635 : (((((True ∨ p2) → False) → False) ∨ (((p4 ∧ True) → (p2 ∧ True)) → False)) ∨ ((((p6 → False) ∧ (p1 → True)) → ((True ∨ p3) → (p5 → False))) → (((p7 → False) → (p0 ∧ True)) → ((p1 ∧ p2) ∨ (p7 → p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (True ∨ p2) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p5 p6 p3 p7 : Prop)
theorem file60_37084 : (((((p6 → False) → (p6 → p5)) → False) → False) ∨ ((((p7 → p7) ∧ (p1 ∨ p3)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p6 → False) → (p6 → p5)) := by
    intro assump_5
    intro assump_6
    have assump_19 : p6 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p5 p7 p0 p3 p1 : Prop)
theorem file60_37554 : ((((((p3 ∧ p2) → (p3 ∨ p7)) ∨ ((False → False) ∧ (p3 ∧ p2))) ∨ (((p5 ∧ p1) → False) ∧ ((p0 ∨ p7) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p3 ∧ p2) → (p3 ∨ p7)) ∨ ((False → False) ∧ (p3 ∧ p2))) ∨ (((p5 ∧ p1) → False) ∧ ((p0 ∨ p7) ∧ (p5 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      exact assump_6
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p5 p2 p3 p7 : Prop)
theorem file60_38118 : (((((p2 ∧ p2) ∧ (False ∧ p5)) ∧ ((p4 → p7) → False)) ∧ (((p5 ∨ p3) ∨ (p2 ∨ p2)) ∧ ((True ∧ p7) ∧ (p5 ∨ p7)))) → False) := by
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
            apply False.elim assump_14


variable (p5 p0 p7 p3 p2 p6 p4 : Prop)
theorem file60_38659 : ((((((p7 → False) → (p0 → p0)) → ((p5 → True) → (p5 → False))) ∧ (((p6 → False) ∨ (p2 ∧ p3)) ∧ ((False → False) ∨ (p6 → False)))) ∧ ((((p7 ∨ p2) → False) → ((p0 → False) → False)) ∧ (((True ∨ p6) → (p4 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              have assump_100 : ((True ∨ p6) → (p4 ∨ True)) := by
                intro assump_25
                cases assump_25
                case inl assump_26 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_27 =>
                  apply Or.inr
                  apply True.intro
              let assump_24 := assump_19 assump_100
              apply False.elim assump_24
          case inr assump_15 =>
            cases assump_3
            case intro assump_37 assump_38 =>
              have assump_101 : ((True ∨ p6) → (p4 ∨ True)) := by
                intro assump_44
                cases assump_44
                case inl assump_45 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_46 =>
                  apply Or.inr
                  apply True.intro
              let assump_43 := assump_38 assump_101
              apply False.elim assump_43
        case inr assump_11 =>
          cases assump_11
          case intro assump_54 assump_55 =>
            cases assump_9
            case inl assump_60 =>
              cases assump_3
              case intro assump_64 assump_65 =>
                have assump_102 : ((True ∨ p6) → (p4 ∨ True)) := by
                  intro assump_71
                  cases assump_71
                  case inl assump_72 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_73 =>
                    apply Or.inr
                    apply True.intro
                let assump_70 := assump_65 assump_102
                apply False.elim assump_70
            case inr assump_61 =>
              cases assump_3
              case intro assump_83 assump_84 =>
                have assump_103 : ((True ∨ p6) → (p4 ∨ True)) := by
                  intro assump_90
                  cases assump_90
                  case inl assump_91 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_92 =>
                    apply Or.inr
                    apply True.intro
                let assump_89 := assump_84 assump_103
                apply False.elim assump_89


variable (p1 p2 p7 p4 p6 p0 p5 : Prop)
theorem file60_41546 : ((((((False ∨ p6) ∨ (p2 ∧ p7)) → ((p0 ∨ p6) ∨ (True → p0))) → (((p2 → p7) ∧ (p1 → False)) → ((False → p2) ∨ (p5 ∧ p4)))) → False) → False) := by
  intro assump_9
  have assump_29 : ((((False ∨ p6) ∨ (p2 ∧ p7)) → ((p0 ∨ p6) ∨ (True → p0))) → (((p2 → p7) ∧ (p1 → False)) → ((False → p2) ∨ (p5 ∧ p4)))) := by
    intro assump_13
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply Or.inl
      intro assump_23
      apply False.elim assump_23
  let assump_12 := assump_9 assump_29
  apply False.elim assump_12


variable (p4 p7 p1 p3 p5 : Prop)
theorem file60_42148 : (((((p1 ∧ True) ∧ (False ∧ p7)) → False) ∧ (((p4 → p5) → (p5 ∧ True)) → False)) → ((((p4 → p4) ∧ (False ∧ p3)) ∧ ((p3 ∧ p4) ∧ (p5 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p5 p6 p0 p2 p1 : Prop)
theorem file60_42596 : ((((((p0 → p0) → False) → ((p0 → p2) → (p5 → False))) ∨ (((p1 ∧ p5) ∧ (p2 ∧ p1)) ∧ ((True → p6) ∨ (p2 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p0 → p0) → False) → ((p0 → p2) → (p5 → False))) ∨ (((p1 ∧ p5) ∧ (p2 ∧ p1)) ∧ ((True → p6) ∨ (p2 ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_25 : (p0 → p0) := by
      intro assump_15
      exact assump_15
    let assump_14 := assump_5 assump_25
    apply False.elim assump_14
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p1 p3 p6 p2 p4 p7 : Prop)
theorem file60_43233 : (((((p2 → p1) ∧ (p7 → p4)) ∨ ((p3 → p7) → False)) → False) → ((((p3 ∧ p4) → False) ∧ ((p4 ∨ True) → False)) → (((p4 ∧ False) → False) ∨ ((True ∧ p6) → False)))) := by
  intro assump_32
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    apply Or.inl
    intro assump_42
    cases assump_42
    case intro assump_43 assump_44 =>
      apply False.elim assump_44


variable (p4 p3 p7 p5 p6 p2 p0 p1 : Prop)
theorem file60_43684 : (((((p5 ∧ p3) ∨ (p5 ∨ p1)) → False) ∧ (((p1 ∧ p5) → (p4 ∨ p6)) ∧ ((p6 ∧ p5) → False))) → ((((False ∧ p5) ∨ (p2 → p7)) → ((p2 → False) → False)) → (((p5 ∧ p0) ∨ (False ∧ p2)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          have assump_34 : ((p5 ∧ p3) ∨ (p5 ∨ p1)) := by
            apply Or.inr
            apply Or.inl
            exact assump_6
          let assump_26 := assump_14 assump_34
          apply False.elim assump_26
  case inr assump_5 =>
    cases assump_5
    case intro assump_30 assump_31 =>
      apply False.elim assump_30


variable (p5 p7 p6 p0 p1 p4 : Prop)
theorem file60_44539 : (((((p5 → False) → (p5 → False)) → False) → False) ∨ ((((p0 → p0) ∨ (False ∨ p1)) → False) ∨ (((p7 → False) ∧ (p6 → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p5 → False) → (p5 → False)) := by
    intro assump_5
    intro assump_6
    have assump_19 : p5 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p7 p4 p3 p1 : Prop)
theorem file60_45046 : ((((((p0 → False) ∨ (True ∧ p4)) ∧ ((p0 → p0) → False)) → (((True → False) ∨ (p7 → False)) → False)) ∧ ((((p3 → False) → (True ∧ True)) ∨ ((p3 → False) → (True ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p3 → False) → (True ∧ True)) ∨ ((p3 → False) → (True ∨ p1))) := by
      apply Or.inl
      intro assump_9
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p1 p5 p0 p3 p4 p7 p6 p2 : Prop)
theorem file60_45641 : (((((p5 → False) ∨ (p0 → p4)) ∨ ((p0 ∧ False) ∧ (p4 ∨ True))) ∨ (((p1 → p2) ∧ (False ∧ p7)) ∨ ((p5 ∨ p6) ∨ (p1 ∧ p2)))) → ((((p5 → False) ∧ (p2 ∨ p5)) ∧ ((p5 → False) → (p2 ∧ p2))) → (((True ∧ False) → False) ∧ ((p4 → True) ∨ (p3 → False))))) := by
  intro assump_9
  intro assump_10
  apply And.intro
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    apply False.elim assump_13
  cases assump_10
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_21
      case inl assump_24 =>
        cases assump_9
        case inl assump_30 =>
          cases assump_30
          case inl assump_32 =>
            cases assump_32
            case inl assump_34 =>
              apply Or.inl
              intro assump_38
              apply True.intro
            case inr assump_35 =>
              apply Or.inl
              intro assump_41
              apply True.intro
          case inr assump_33 =>
            cases assump_33
            case intro assump_42 assump_43 =>
              cases assump_42
              case intro assump_44 assump_45 =>
                apply False.elim assump_45
        case inr assump_31 =>
          cases assump_31
          case inl assump_50 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_53
              case intro assump_56 assump_57 =>
                apply False.elim assump_56
          case inr assump_51 =>
            cases assump_51
            case inl assump_60 =>
              cases assump_60
              case inl assump_62 =>
                apply Or.inl
                intro assump_66
                apply True.intro
              case inr assump_63 =>
                apply Or.inl
                intro assump_69
                apply True.intro
            case inr assump_61 =>
              cases assump_61
              case intro assump_70 assump_71 =>
                apply Or.inl
                intro assump_76
                apply True.intro
      case inr assump_25 =>
        cases assump_9
        case inl assump_81 =>
          cases assump_81
          case inl assump_83 =>
            cases assump_83
            case inl assump_85 =>
              apply Or.inl
              intro assump_89
              apply True.intro
            case inr assump_86 =>
              apply Or.inl
              intro assump_92
              apply True.intro
          case inr assump_84 =>
            cases assump_84
            case intro assump_93 assump_94 =>
              cases assump_93
              case intro assump_95 assump_96 =>
                apply False.elim assump_96
        case inr assump_82 =>
          cases assump_82
          case inl assump_101 =>
            cases assump_101
            case intro assump_103 assump_104 =>
              cases assump_104
              case intro assump_107 assump_108 =>
                apply False.elim assump_107
          case inr assump_102 =>
            cases assump_102
            case inl assump_111 =>
              cases assump_111
              case inl assump_113 =>
                apply Or.inl
                intro assump_117
                apply True.intro
              case inr assump_114 =>
                apply Or.inl
                intro assump_120
                apply True.intro
            case inr assump_112 =>
              cases assump_112
              case intro assump_121 assump_122 =>
                apply Or.inl
                intro assump_127
                apply True.intro


variable (p4 p6 p5 p1 : Prop)
theorem file60_49277 : (((((p1 ∨ p6) → (p5 ∨ p4)) ∧ ((p4 ∧ False) ∨ (p5 → False))) ∧ (((p5 → p5) ∨ (False ∧ p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_9 =>
        have assump_27 : ((p5 → p5) ∨ (False ∧ p1)) := by
          apply Or.inl
          intro assump_21
          exact assump_21
        let assump_20 := assump_3 assump_27
        apply False.elim assump_20


variable (p4 p7 p0 p2 p6 : Prop)
theorem file60_49961 : ((((((p4 → p2) ∨ (False → False)) ∧ ((p0 ∧ p0) ∧ (p0 → False))) → (((p2 → False) → (False → False)) ∨ ((p7 ∧ p6) → (p6 ∧ p0)))) → False) → False) := by
  intro assump_10
  have assump_54 : ((((p4 → p2) ∨ (False → False)) ∧ ((p0 ∧ p0) ∧ (p0 → False))) → (((p2 → False) → (False → False)) ∨ ((p7 ∧ p6) → (p6 ∧ p0)))) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        cases assump_16
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            apply Or.inl
            intro assump_31
            intro assump_32
            apply False.elim assump_32
      case inr assump_18 =>
        cases assump_16
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            apply Or.inl
            intro assump_47
            intro assump_48
            apply False.elim assump_48
  let assump_13 := assump_10 assump_54
  apply False.elim assump_13


variable (p2 p5 p3 p4 p0 p7 p1 : Prop)
theorem file60_51081 : (((((p3 → p2) → False) → ((True ∧ p3) → (p1 ∨ p4))) ∧ (((p7 ∨ False) → (p5 → p0)) ∧ ((True → False) ∧ (p2 ∧ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_26 : True := by
            apply True.intro
          let assump_22 := assump_10 assump_26
          apply False.elim assump_22


variable (p3 p0 p4 : Prop)
theorem file60_51663 : (((((False → p4) → False) → False) → False) → ((((p3 → False) ∧ (False ∧ p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_21 : (((False → p4) → False) → False) := by
    intro assump_8
    have assump_22 : (False → p4) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_8 assump_22
    apply False.elim assump_11
  let assump_7 := assump_1 assump_21
  apply False.elim assump_7


variable (p3 p6 p4 p5 p7 p2 p0 : Prop)
theorem file60_52171 : (((((p7 ∨ p5) ∨ (p0 ∨ True)) → False) ∧ (((True → False) ∨ (True → False)) ∨ ((p5 ∧ p6) ∧ (True → True)))) → ((((p2 ∨ p6) ∨ (p3 → False)) → ((p0 → False) ∧ (p0 → False))) ∧ (((p7 → False) ∧ (p3 ∨ p0)) → ((p0 ∨ p4) → False)))) := by
  intro assump_26
  apply And.intro
  intro assump_27
  apply And.intro
  intro assump_28
  cases assump_27
  case inl assump_31 =>
    cases assump_31
    case inl assump_33 =>
      cases assump_26
      case intro assump_37 assump_38 =>
        cases assump_38
        case inl assump_41 =>
          cases assump_41
          case inl assump_43 =>
            have assump_462 : True := by
              apply True.intro
            let assump_47 := assump_43 assump_462
            apply False.elim assump_47
          case inr assump_44 =>
            have assump_463 : True := by
              apply True.intro
            let assump_53 := assump_44 assump_463
            apply False.elim assump_53
        case inr assump_42 =>
          cases assump_42
          case intro assump_57 assump_58 =>
            cases assump_57
            case intro assump_59 assump_60 =>
              have assump_464 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                apply Or.inl
                apply Or.inr
                exact assump_59
              let assump_71 := assump_37 assump_464
              apply False.elim assump_71
    case inr assump_34 =>
      cases assump_26
      case intro assump_77 assump_78 =>
        cases assump_78
        case inl assump_81 =>
          cases assump_81
          case inl assump_83 =>
            have assump_465 : True := by
              apply True.intro
            let assump_87 := assump_83 assump_465
            apply False.elim assump_87
          case inr assump_84 =>
            have assump_466 : True := by
              apply True.intro
            let assump_93 := assump_84 assump_466
            apply False.elim assump_93
        case inr assump_82 =>
          cases assump_82
          case intro assump_97 assump_98 =>
            cases assump_97
            case intro assump_99 assump_100 =>
              have assump_467 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                apply Or.inl
                apply Or.inr
                exact assump_99
              let assump_111 := assump_77 assump_467
              apply False.elim assump_111
  case inr assump_32 =>
    cases assump_26
    case intro assump_117 assump_118 =>
      cases assump_118
      case inl assump_121 =>
        cases assump_121
        case inl assump_123 =>
          have assump_468 : True := by
            apply True.intro
          let assump_127 := assump_123 assump_468
          apply False.elim assump_127
        case inr assump_124 =>
          have assump_469 : True := by
            apply True.intro
          let assump_133 := assump_124 assump_469
          apply False.elim assump_133
      case inr assump_122 =>
        cases assump_122
        case intro assump_137 assump_138 =>
          cases assump_137
          case intro assump_139 assump_140 =>
            have assump_470 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
              apply Or.inl
              apply Or.inr
              exact assump_139
            let assump_151 := assump_117 assump_470
            apply False.elim assump_151
  intro assump_155
  cases assump_27
  case inl assump_158 =>
    cases assump_158
    case inl assump_160 =>
      cases assump_26
      case intro assump_164 assump_165 =>
        cases assump_165
        case inl assump_168 =>
          cases assump_168
          case inl assump_170 =>
            have assump_471 : True := by
              apply True.intro
            let assump_174 := assump_170 assump_471
            apply False.elim assump_174
          case inr assump_171 =>
            have assump_472 : True := by
              apply True.intro
            let assump_180 := assump_171 assump_472
            apply False.elim assump_180
        case inr assump_169 =>
          cases assump_169
          case intro assump_184 assump_185 =>
            cases assump_184
            case intro assump_186 assump_187 =>
              have assump_473 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                apply Or.inl
                apply Or.inr
                exact assump_186
              let assump_198 := assump_164 assump_473
              apply False.elim assump_198
    case inr assump_161 =>
      cases assump_26
      case intro assump_204 assump_205 =>
        cases assump_205
        case inl assump_208 =>
          cases assump_208
          case inl assump_210 =>
            have assump_474 : True := by
              apply True.intro
            let assump_214 := assump_210 assump_474
            apply False.elim assump_214
          case inr assump_211 =>
            have assump_475 : True := by
              apply True.intro
            let assump_220 := assump_211 assump_475
            apply False.elim assump_220
        case inr assump_209 =>
          cases assump_209
          case intro assump_224 assump_225 =>
            cases assump_224
            case intro assump_226 assump_227 =>
              have assump_476 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                apply Or.inl
                apply Or.inr
                exact assump_226
              let assump_238 := assump_204 assump_476
              apply False.elim assump_238
  case inr assump_159 =>
    cases assump_26
    case intro assump_244 assump_245 =>
      cases assump_245
      case inl assump_248 =>
        cases assump_248
        case inl assump_250 =>
          have assump_477 : True := by
            apply True.intro
          let assump_254 := assump_250 assump_477
          apply False.elim assump_254
        case inr assump_251 =>
          have assump_478 : True := by
            apply True.intro
          let assump_260 := assump_251 assump_478
          apply False.elim assump_260
      case inr assump_249 =>
        cases assump_249
        case intro assump_264 assump_265 =>
          cases assump_264
          case intro assump_266 assump_267 =>
            have assump_479 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
              apply Or.inl
              apply Or.inr
              exact assump_266
            let assump_278 := assump_244 assump_479
            apply False.elim assump_278
  intro assump_282
  intro assump_283
  cases assump_283
  case inl assump_284 =>
    cases assump_282
    case intro assump_288 assump_289 =>
      cases assump_289
      case inl assump_292 =>
        cases assump_26
        case intro assump_296 assump_297 =>
          cases assump_297
          case inl assump_300 =>
            cases assump_300
            case inl assump_302 =>
              have assump_480 : True := by
                apply True.intro
              let assump_306 := assump_302 assump_480
              apply False.elim assump_306
            case inr assump_303 =>
              have assump_481 : True := by
                apply True.intro
              let assump_312 := assump_303 assump_481
              apply False.elim assump_312
          case inr assump_301 =>
            cases assump_301
            case intro assump_316 assump_317 =>
              cases assump_316
              case intro assump_318 assump_319 =>
                have assump_482 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_318
                let assump_330 := assump_296 assump_482
                apply False.elim assump_330
      case inr assump_293 =>
        cases assump_26
        case intro assump_336 assump_337 =>
          cases assump_337
          case inl assump_340 =>
            cases assump_340
            case inl assump_342 =>
              have assump_483 : True := by
                apply True.intro
              let assump_346 := assump_342 assump_483
              apply False.elim assump_346
            case inr assump_343 =>
              have assump_484 : True := by
                apply True.intro
              let assump_352 := assump_343 assump_484
              apply False.elim assump_352
          case inr assump_341 =>
            cases assump_341
            case intro assump_356 assump_357 =>
              cases assump_356
              case intro assump_358 assump_359 =>
                have assump_485 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_358
                let assump_370 := assump_336 assump_485
                apply False.elim assump_370
  case inr assump_285 =>
    cases assump_282
    case intro assump_376 assump_377 =>
      cases assump_377
      case inl assump_380 =>
        cases assump_26
        case intro assump_384 assump_385 =>
          cases assump_385
          case inl assump_388 =>
            cases assump_388
            case inl assump_390 =>
              have assump_486 : True := by
                apply True.intro
              let assump_394 := assump_390 assump_486
              apply False.elim assump_394
            case inr assump_391 =>
              have assump_487 : True := by
                apply True.intro
              let assump_400 := assump_391 assump_487
              apply False.elim assump_400
          case inr assump_389 =>
            cases assump_389
            case intro assump_404 assump_405 =>
              cases assump_404
              case intro assump_406 assump_407 =>
                have assump_488 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_406
                let assump_418 := assump_384 assump_488
                apply False.elim assump_418
      case inr assump_381 =>
        cases assump_26
        case intro assump_424 assump_425 =>
          cases assump_425
          case inl assump_428 =>
            cases assump_428
            case inl assump_430 =>
              have assump_489 : True := by
                apply True.intro
              let assump_434 := assump_430 assump_489
              apply False.elim assump_434
            case inr assump_431 =>
              have assump_490 : True := by
                apply True.intro
              let assump_440 := assump_431 assump_490
              apply False.elim assump_440
          case inr assump_429 =>
            cases assump_429
            case intro assump_444 assump_445 =>
              cases assump_444
              case intro assump_446 assump_447 =>
                have assump_491 : ((p7 ∨ p5) ∨ (p0 ∨ True)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_446
                let assump_458 := assump_424 assump_491
                apply False.elim assump_458


variable (p7 p1 p3 p0 : Prop)
theorem file60_63027 : (((((p3 ∧ p3) ∧ (p7 ∧ p1)) → ((True → False) → (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_37 : (((p3 ∧ p3) ∧ (p7 ∧ p1)) → ((True → False) → (p0 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_13
        case intro assump_20 assump_21 =>
          have assump_38 : True := by
            apply True.intro
          let assump_30 := assump_6 assump_38
          apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p7 p5 p3 p6 p1 p4 p2 p0 : Prop)
theorem file60_63738 : (((((p0 ∨ p1) → False) ∧ ((p5 → False) ∧ (True ∨ True))) → (((p0 ∧ p2) → False) ∨ ((False ∨ p0) → (p2 ∨ p0)))) ∨ ((((p7 ∧ p5) ∧ (p1 ∨ p3)) → ((p5 ∧ True) ∧ (p0 → p2))) → (((False → p2) ∨ (p4 ∧ p1)) ∨ ((p0 → False) → (p6 ∨ p7))))) := by
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        apply Or.inl
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          have assump_47 : (p0 ∨ p1) := by
            apply Or.inl
            exact assump_18
          let assump_27 := assump_5 assump_47
          apply False.elim assump_27
      case inr assump_14 =>
        apply Or.inl
        intro assump_33
        cases assump_33
        case intro assump_34 assump_35 =>
          have assump_48 : (p0 ∨ p1) := by
            apply Or.inl
            exact assump_34
          let assump_43 := assump_5 assump_48
          apply False.elim assump_43


variable (p6 p3 p7 p5 p4 p1 : Prop)
theorem file60_64831 : (((((False → p7) ∨ (p1 ∨ p6)) ∨ ((p5 → p4) → (p6 ∧ p3))) ∧ (((False → False) → False) ∧ ((p4 ∨ False) → (p4 ∨ True)))) → False) := by
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_30
    case inl assump_32 =>
      cases assump_32
      case inl assump_34 =>
        cases assump_31
        case intro assump_38 assump_39 =>
          have assump_102 : (False → False) := by
            intro assump_46
            apply False.elim assump_46
          let assump_45 := assump_38 assump_102
          apply False.elim assump_45
      case inr assump_35 =>
        cases assump_35
        case inl assump_52 =>
          cases assump_31
          case intro assump_56 assump_57 =>
            have assump_103 : (False → False) := by
              intro assump_64
              apply False.elim assump_64
            let assump_63 := assump_56 assump_103
            apply False.elim assump_63
        case inr assump_53 =>
          cases assump_31
          case intro assump_72 assump_73 =>
            have assump_104 : (False → False) := by
              intro assump_80
              apply False.elim assump_80
            let assump_79 := assump_72 assump_104
            apply False.elim assump_79
    case inr assump_33 =>
      cases assump_31
      case intro assump_88 assump_89 =>
        have assump_105 : (False → False) := by
          intro assump_96
          apply False.elim assump_96
        let assump_95 := assump_88 assump_105
        apply False.elim assump_95


variable (p7 p3 p5 p1 p0 : Prop)
theorem file60_66414 : ((((((p1 ∨ p3) → False) ∨ ((True ∨ False) → (p3 → p1))) → (((p0 ∨ p5) ∨ (p5 → False)) ∨ ((False ∧ p7) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((p1 ∨ p3) → False) ∨ ((True ∨ False) → (p3 → p1))) → (((p0 ∨ p5) ∨ (p5 → False)) ∨ ((False ∧ p7) → (p0 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inr
      intro assump_10
      have assump_49 : ((((p1 ∨ p3) → False) ∨ ((True ∨ False) → (p3 → p1))) → (((p0 ∨ p5) ∨ (p5 → False)) ∨ ((False ∧ p7) → (p0 → False)))) := by
        intro assump_16
        cases assump_16
        case inl assump_17 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_10
        case inr assump_18 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_10
      let assump_15 := assump_1 assump_49
      apply False.elim assump_15
    case inr assump_7 =>
      apply Or.inl
      apply Or.inr
      intro assump_28
      have assump_50 : ((((p1 ∨ p3) → False) ∨ ((True ∨ False) → (p3 → p1))) → (((p0 ∨ p5) ∨ (p5 → False)) ∨ ((False ∧ p7) → (p0 → False)))) := by
        intro assump_35
        cases assump_35
        case inl assump_36 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_28
        case inr assump_37 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_28
      let assump_34 := assump_1 assump_50
      apply False.elim assump_34
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p1 p3 p7 p4 p0 p6 : Prop)
theorem file60_68091 : (((((p3 ∨ p1) ∨ (False ∨ True)) ∨ ((False ∧ p6) ∧ (False ∨ p6))) ∨ (((p3 → p0) ∧ (p7 → p3)) → False)) ∨ ((((p0 → p6) → False) ∨ ((False ∧ True) ∧ (p4 ∨ p6))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p6 p2 p3 p4 p1 p0 : Prop)
theorem file60_68419 : ((((((p0 → False) → (p2 → p1)) ∧ ((p6 ∧ p3) → (p4 → False))) → (((p3 → p0) → (False → p4)) ∨ ((p0 ∧ False) ∨ (p4 → True)))) → False) → False) := by
  intro assump_9
  have assump_27 : ((((p0 → False) → (p2 → p1)) ∧ ((p6 ∧ p3) → (p4 → False))) → (((p3 → p0) → (False → p4)) ∨ ((p0 ∧ False) ∨ (p4 → True)))) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply Or.inl
      intro assump_20
      intro assump_21
      apply False.elim assump_21
  let assump_12 := assump_9 assump_27
  apply False.elim assump_12


variable (p3 p5 p0 : Prop)
theorem file60_69023 : ((((((True ∨ p0) → False) ∧ ((p5 ∧ p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((True ∨ p0) → False) ∧ ((p5 ∧ p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p5 p3 p2 : Prop)
theorem file60_69555 : (((((p2 → False) → False) → False) ∧ (((p3 → False) ∨ (False ∨ p5)) → ((p5 → False) → False))) → ((((p3 → False) ∧ (p5 → False)) → False) ∨ (((False ∧ True) → False) → ((True → True) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_39 : ((p3 → False) ∨ (False ∨ p5)) := by
        apply Or.inl
        intro assump_18
        have assump_40 : p3 := by
          exact assump_18
        let assump_23 := assump_9 assump_40
        apply False.elim assump_23
      let assump_17 := assump_3 assump_39
      have assump_41 : (p5 → False) := by
        intro assump_28
        have assump_42 : p5 := by
          exact assump_28
        let assump_32 := assump_10 assump_42
        apply False.elim assump_32
      let assump_27 := assump_17 assump_41
      apply False.elim assump_27


variable (p1 p0 p4 p3 p2 p6 p7 : Prop)
theorem file60_70546 : (((((True → False) → False) ∧ ((p1 ∧ p6) ∧ (p1 → False))) ∧ (((p6 → p3) ∨ (p2 → False)) ∧ ((p6 ∨ p1) ∨ (p7 → False)))) → ((((p3 → p0) → (True ∧ p7)) → False) → (((p3 → False) → (p4 → False)) → ((p0 → p4) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_12
          case intro assump_27 assump_28 =>
            cases assump_27
            case inl assump_29 =>
              cases assump_28
              case inl assump_33 =>
                cases assump_33
                case inl assump_35 =>
                  have assump_94 : p1 := by
                    exact assump_19
                  let assump_42 := assump_18 assump_94
                  apply False.elim assump_42
                case inr assump_36 =>
                  have assump_95 : p1 := by
                    exact assump_36
                  let assump_51 := assump_18 assump_95
                  apply False.elim assump_51
              case inr assump_34 =>
                have assump_96 : p1 := by
                  exact assump_19
                let assump_60 := assump_18 assump_96
                apply False.elim assump_60
            case inr assump_30 =>
              cases assump_28
              case inl assump_66 =>
                cases assump_66
                case inl assump_68 =>
                  have assump_97 : p1 := by
                    exact assump_19
                  let assump_74 := assump_18 assump_97
                  apply False.elim assump_74
                case inr assump_69 =>
                  have assump_98 : p1 := by
                    exact assump_69
                  let assump_82 := assump_18 assump_98
                  apply False.elim assump_82
              case inr assump_67 =>
                have assump_99 : p1 := by
                  exact assump_19
                let assump_90 := assump_18 assump_99
                apply False.elim assump_90


variable (p2 p3 p5 p4 p0 : Prop)
theorem file60_72782 : ((((((p3 → False) → (p4 → False)) ∧ ((p5 → False) → False)) → False) ∧ ((((True ∧ p3) → False) → False) ∧ (((p2 → True) → False) ∧ ((p4 → False) ∨ (p5 → p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          have assump_32 : (p2 → True) := by
            intro assump_20
            apply True.intro
          let assump_19 := assump_10 assump_32
          apply False.elim assump_19
        case inr assump_15 =>
          have assump_33 : (p2 → True) := by
            intro assump_28
            apply True.intro
          let assump_27 := assump_10 assump_33
          apply False.elim assump_27


variable (p7 p0 p6 p5 p1 p4 p2 p3 : Prop)
theorem file60_73664 : (((((p1 → p3) ∧ (p6 ∧ False)) → ((p2 → False) ∧ (p0 → p1))) → False) → ((((p5 ∧ p3) → False) ∧ ((True ∨ p0) → False)) ∧ (((p7 ∧ p7) → (p7 → p5)) ∨ ((p3 ∧ p7) ∨ (p0 ∧ p4))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_161 : (((p1 → p3) ∧ (p6 ∧ False)) → ((p2 → False) ∧ (p0 → p1))) := by
      intro assump_12
      apply And.intro
      intro assump_13
      cases assump_12
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
      intro assump_26
      cases assump_12
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          apply False.elim assump_34
    let assump_11 := assump_1 assump_161
    apply False.elim assump_11
  intro assump_42
  cases assump_42
  case inl assump_43 =>
    have assump_162 : (((p1 → p3) ∧ (p6 ∧ False)) → ((p2 → False) ∧ (p0 → p1))) := by
      intro assump_50
      apply And.intro
      intro assump_51
      cases assump_50
      case intro assump_54 assump_55 =>
        cases assump_55
        case intro assump_58 assump_59 =>
          apply False.elim assump_59
      intro assump_64
      cases assump_50
      case intro assump_67 assump_68 =>
        cases assump_68
        case intro assump_71 assump_72 =>
          apply False.elim assump_72
    let assump_49 := assump_1 assump_162
    apply False.elim assump_49
  case inr assump_44 =>
    have assump_163 : (((p1 → p3) ∧ (p6 ∧ False)) → ((p2 → False) ∧ (p0 → p1))) := by
      intro assump_85
      apply And.intro
      intro assump_86
      cases assump_85
      case intro assump_89 assump_90 =>
        cases assump_90
        case intro assump_93 assump_94 =>
          apply False.elim assump_94
      intro assump_99
      cases assump_85
      case intro assump_102 assump_103 =>
        cases assump_103
        case intro assump_106 assump_107 =>
          apply False.elim assump_107
    let assump_84 := assump_1 assump_163
    apply False.elim assump_84
  apply Or.inl
  intro assump_117
  intro assump_118
  cases assump_117
  case intro assump_121 assump_122 =>
    have assump_164 : (((p1 → p3) ∧ (p6 ∧ False)) → ((p2 → False) ∧ (p0 → p1))) := by
      intro assump_131
      apply And.intro
      intro assump_132
      cases assump_131
      case intro assump_135 assump_136 =>
        cases assump_136
        case intro assump_139 assump_140 =>
          apply False.elim assump_140
      intro assump_145
      cases assump_131
      case intro assump_148 assump_149 =>
        cases assump_149
        case intro assump_152 assump_153 =>
          apply False.elim assump_153
    let assump_130 := assump_1 assump_164
    apply False.elim assump_130


variable (p5 p1 p6 p3 p2 p7 p4 p0 : Prop)
theorem file60_76554 : (((((False → False) → False) → ((p0 ∨ False) → False)) → False) → ((((p6 → p4) → (p7 → p6)) → ((False ∨ p2) → False)) → (((p5 ∨ p7) → (False → False)) → ((p1 → p3) → (p7 ∧ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  have assump_63 : (((False → False) → False) → ((p0 ∨ False) → False)) := by
    intro assump_14
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      have assump_64 : (False → False) := by
        intro assump_23
        apply False.elim assump_23
      let assump_22 := assump_14 assump_64
      apply False.elim assump_22
    case inr assump_17 =>
      apply False.elim assump_17
  let assump_13 := assump_1 assump_63
  apply False.elim assump_13
  have assump_65 : (((False → False) → False) → ((p0 ∨ False) → False)) := by
    intro assump_43
    intro assump_44
    cases assump_44
    case inl assump_45 =>
      have assump_66 : (False → False) := by
        intro assump_52
        apply False.elim assump_52
      let assump_51 := assump_43 assump_66
      apply False.elim assump_51
    case inr assump_46 =>
      apply False.elim assump_46
  let assump_42 := assump_1 assump_65
  apply False.elim assump_42


variable (p0 p5 p6 p3 p7 p1 : Prop)
theorem file60_77826 : ((((((p1 → False) ∧ (True → False)) → ((p5 → p6) → False)) ∨ (((p5 ∧ p0) ∨ (p7 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p1 → False) ∧ (True → False)) → ((p5 → p6) → False)) ∨ (((p5 ∧ p0) ∨ (p7 → p3)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_23 : True := by
        apply True.intro
      let assump_15 := assump_10 assump_23
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p5 p4 p1 : Prop)
theorem file60_78444 : (((((p4 → False) ∧ (p5 → p1)) ∧ ((False ∧ p1) ∧ (p4 ∧ p1))) ∨ (((True → False) → False) → False)) → False) := by
  intro assump_20
  cases assump_20
  case inl assump_21 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_24
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            apply False.elim assump_33
  case inr assump_22 =>
    have assump_50 : ((True → False) → False) := by
      intro assump_40
      have assump_51 : True := by
        apply True.intro
      let assump_43 := assump_40 assump_51
      apply False.elim assump_43
    let assump_39 := assump_22 assump_50
    apply False.elim assump_39


variable (p6 p4 p2 p3 p5 p1 p7 : Prop)
theorem file60_79280 : ((((((p7 → False) ∧ (p1 → False)) ∨ ((p4 → True) ∨ (p3 ∨ p2))) → (((p5 → False) ∧ (p6 ∨ p4)) ∨ ((p1 ∧ False) ∨ (p7 → p2)))) ∧ ((((True ∨ p5) → False) → ((p6 ∧ p5) → (p4 ∨ p2))) → (((True ∨ True) → False) ∧ ((True ∨ p6) ∧ (p1 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((True ∨ p5) → False) → ((p6 ∧ p5) → (p4 ∨ p2))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_29 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_19 := assump_9 assump_29
        apply False.elim assump_19
    let assump_8 := assump_3 assump_28
    let assump_23 := And.left assump_8
    have assump_30 : (True ∨ True) := by
      apply Or.inl
      apply True.intro
    let assump_24 := assump_23 assump_30
    apply False.elim assump_24


variable (p4 p1 p7 p0 p5 p2 p3 p6 : Prop)
theorem file60_80254 : (((((p5 ∧ False) → (p3 ∨ p3)) ∨ ((p1 → False) ∧ (p3 → p4))) ∨ (((p2 → p0) ∨ (p7 ∨ p1)) → ((True → p3) ∨ (p2 → False)))) ∨ ((((p6 ∧ p2) ∧ (p4 → False)) ∧ ((p4 ∨ p7) → False)) ∧ (((p0 ∨ p1) ∧ (p4 → False)) ∧ ((p7 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p7 p2 p6 p5 : Prop)
theorem file60_80686 : ((((((p7 → p5) → False) ∨ ((p2 → False) → (p2 → False))) → (((False → False) → (p6 → True)) ∨ ((False → False) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 → p5) → False) ∨ ((p2 → False) → (p2 → False))) → (((False → False) → (p6 → True)) ∨ ((False → False) ∨ (p2 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_14
      intro assump_15
      apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p4 p7 p2 p5 p6 : Prop)
theorem file60_81393 : (((((p6 ∧ p4) ∨ (True → False)) → False) ∨ (((p6 ∨ p1) → (p7 ∧ p1)) ∧ ((p5 ∨ p2) → False))) → ((((False ∧ False) → (p2 ∧ p4)) ∨ ((False ∧ p2) ∧ (p7 → p4))) ∨ (((p4 → False) ∧ (p2 → False)) ∨ ((p2 ∧ p1) → (p1 → p4))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
    cases assump_6
    case intro assump_11 assump_12 =>
      apply False.elim assump_11
  case inr assump_3 =>
    cases assump_3
    case intro assump_15 assump_16 =>
      apply Or.inl
      apply Or.inl
      intro assump_21
      apply And.intro
      cases assump_21
      case intro assump_22 assump_23 =>
        apply False.elim assump_22
      cases assump_21
      case intro assump_26 assump_27 =>
        apply False.elim assump_26


variable (p2 p6 p0 p7 : Prop)
theorem file60_82334 : ((((((p6 ∨ False) ∧ (p7 ∧ p2)) ∨ ((p6 ∧ False) → False)) ∨ (((p0 ∨ False) ∨ (p2 ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 ∨ False) ∧ (p7 ∧ p2)) ∨ ((p6 ∧ False) → False)) ∨ (((p0 ∨ False) ∨ (p2 ∨ False)) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p7 p3 p6 p0 p1 : Prop)
theorem file60_82863 : ((((((p3 → False) ∨ (p1 → False)) → ((p2 ∧ True) → False)) ∧ (((p6 ∧ p0) → False) → ((p1 ∨ p0) ∨ (True ∧ False)))) ∧ ((((p0 ∨ p3) ∨ (True → True)) → False) ∧ (((p7 → False) ∨ (p6 → p0)) ∨ ((p6 → False) ∧ (p6 → False))))) → False) := by
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
            have assump_51 : ((p0 ∨ p3) ∨ (True → True)) := by
              apply Or.inr
              intro assump_26
              apply True.intro
            let assump_25 := assump_14 assump_51
            apply False.elim assump_25
          case inr assump_21 =>
            have assump_52 : ((p0 ∨ p3) ∨ (True → True)) := by
              apply Or.inr
              intro assump_34
              apply True.intro
            let assump_33 := assump_14 assump_52
            apply False.elim assump_33
        case inr assump_19 =>
          cases assump_19
          case intro assump_38 assump_39 =>
            have assump_53 : ((p0 ∨ p3) ∨ (True → True)) := by
              apply Or.inr
              intro assump_47
              apply True.intro
            let assump_46 := assump_14 assump_53
            apply False.elim assump_46


variable (p4 p2 p0 p5 p7 : Prop)
theorem file60_84301 : (((((p0 → p2) → (False ∨ True)) ∨ ((p7 ∨ p7) → False)) ∨ (((p7 ∧ True) ∨ (p2 ∨ p0)) → False)) ∨ ((((False ∧ p7) → False) ∧ ((p0 → False) ∧ (p4 ∨ p5))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p2 p3 p4 p5 p7 p1 p0 : Prop)
theorem file60_84627 : (((((p2 → False) ∧ (p0 ∨ False)) ∨ ((p3 → p1) ∧ (p0 ∨ p2))) → (((p5 ∧ p1) ∧ (p7 ∧ p2)) → False)) → ((((False ∧ False) ∧ (p7 ∧ p2)) ∧ ((p4 → p5) ∧ (True ∨ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p5 p0 p4 p1 : Prop)
theorem file60_85090 : ((((((p1 ∧ p4) ∨ (False → p0)) ∧ ((False ∧ p4) ∧ (p1 ∧ p5))) ∨ (((False ∧ p5) → (p1 → False)) ∨ ((p0 → False) → (p4 → p4)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p1 ∧ p4) ∨ (False → p0)) ∧ ((False ∧ p4) ∧ (p1 ∧ p5))) ∨ (((False ∧ p5) → (p1 → False)) ∨ ((p0 → False) → (p4 → p4)))) := by
    apply Or.inr
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p3 p2 p5 p0 p6 p4 p1 : Prop)
theorem file60_85697 : (((((p6 → False) ∧ (p2 ∧ p7)) ∧ ((p2 → False) ∨ (p2 ∨ p5))) ∧ (((p4 → True) → False) ∨ ((p2 ∧ p1) → (p1 ∨ p0)))) → ((((False → False) → False) → ((p3 → False) ∨ (True → p5))) ∨ (((p1 → p6) → False) ∧ ((p4 ∧ True) → (p7 ∧ p1))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_9
          case inl assump_20 =>
            cases assump_7
            case inl assump_24 =>
              apply Or.inl
              intro assump_28
              apply Or.inl
              intro assump_31
              have assump_132 : (False → False) := by
                intro assump_36
                apply False.elim assump_36
              let assump_35 := assump_28 assump_132
              apply False.elim assump_35
            case inr assump_25 =>
              apply Or.inl
              intro assump_44
              apply Or.inl
              intro assump_47
              have assump_133 : (False → False) := by
                intro assump_52
                apply False.elim assump_52
              let assump_51 := assump_44 assump_133
              apply False.elim assump_51
          case inr assump_21 =>
            cases assump_21
            case inl assump_58 =>
              cases assump_7
              case inl assump_62 =>
                apply Or.inl
                intro assump_66
                apply Or.inl
                intro assump_69
                have assump_134 : (False → False) := by
                  intro assump_74
                  apply False.elim assump_74
                let assump_73 := assump_66 assump_134
                apply False.elim assump_73
              case inr assump_63 =>
                apply Or.inl
                intro assump_82
                apply Or.inl
                intro assump_85
                have assump_135 : (False → False) := by
                  intro assump_90
                  apply False.elim assump_90
                let assump_89 := assump_82 assump_135
                apply False.elim assump_89
            case inr assump_59 =>
              cases assump_7
              case inl assump_98 =>
                apply Or.inl
                intro assump_102
                apply Or.inl
                intro assump_105
                have assump_136 : (False → False) := by
                  intro assump_110
                  apply False.elim assump_110
                let assump_109 := assump_102 assump_136
                apply False.elim assump_109
              case inr assump_99 =>
                apply Or.inl
                intro assump_118
                apply Or.inl
                intro assump_121
                have assump_137 : (False → False) := by
                  intro assump_126
                  apply False.elim assump_126
                let assump_125 := assump_118 assump_137
                apply False.elim assump_125


variable (p0 p6 p5 p2 : Prop)
theorem file60_88820 : ((((((p5 → True) → False) → False) ∨ (((p5 ∨ True) → False) ∧ ((p6 ∧ p2) ∨ (p0 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p5 → True) → False) → False) ∨ (((p5 ∨ True) → False) ∧ ((p6 ∧ p2) ∨ (p0 ∧ p5)))) := by
    apply Or.inl
    intro assump_5
    have assump_17 : (p5 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p7 p1 p2 p6 p4 p0 p3 : Prop)
theorem file60_89379 : (((((p1 → p5) → (p4 → p5)) ∨ ((False → p3) ∧ (p4 → p5))) → (((p7 ∧ False) ∧ (True → False)) → False)) ∨ ((((p7 → p6) ∨ (p1 ∨ False)) → ((False ∨ p4) → False)) → (((False ∧ p6) → False) ∨ ((p2 ∧ p0) ∧ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6


variable (p3 p7 p4 p5 p6 p1 p2 : Prop)
theorem file60_89852 : (((((False ∨ p6) ∨ (p2 → False)) ∧ ((p6 → p2) ∨ (False → p3))) → False) → ((((p4 ∧ p2) ∧ (p1 ∨ False)) ∧ ((p1 ∧ p5) ∧ (False → False))) → (((p6 ∨ p5) ∨ (p7 ∧ p7)) → ((False → False) ∨ (p4 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case inl assump_20 =>
              cases assump_11
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  apply Or.inl
                  intro assump_36
                  apply False.elim assump_36
            case inr assump_21 =>
              apply False.elim assump_21
    case inr assump_7 =>
      cases assump_2
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          cases assump_45
          case intro assump_47 assump_48 =>
            cases assump_46
            case inl assump_53 =>
              cases assump_44
              case intro assump_57 assump_58 =>
                cases assump_57
                case intro assump_59 assump_60 =>
                  apply Or.inl
                  intro assump_69
                  apply False.elim assump_69
            case inr assump_54 =>
              apply False.elim assump_54
  case inr assump_5 =>
    cases assump_5
    case intro assump_74 assump_75 =>
      cases assump_2
      case intro assump_80 assump_81 =>
        cases assump_80
        case intro assump_82 assump_83 =>
          cases assump_82
          case intro assump_84 assump_85 =>
            cases assump_83
            case inl assump_90 =>
              cases assump_81
              case intro assump_94 assump_95 =>
                cases assump_94
                case intro assump_96 assump_97 =>
                  apply Or.inl
                  intro assump_106
                  apply False.elim assump_106
            case inr assump_91 =>
              apply False.elim assump_91


variable (p1 p2 p7 p0 p3 p4 : Prop)
theorem file60_92170 : (((((p2 → False) → False) → ((p1 ∨ p4) → (p0 ∨ p3))) ∨ (((p3 ∨ p3) ∧ (p7 ∨ p3)) → False)) → ((((p3 → False) ∧ (False ∧ p3)) ∧ ((p4 ∧ p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p4 p1 p7 p3 p5 : Prop)
theorem file60_92624 : ((((((p4 → p1) ∧ (p1 ∧ p5)) → ((p3 ∨ p5) ∧ (p7 → p1))) ∨ (((p3 ∨ p4) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p4 → p1) ∧ (p1 ∧ p5)) → ((p3 ∨ p5) ∧ (p7 → p1))) ∨ (((p3 ∨ p4) → False) → False)) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inr
        exact assump_11
    intro assump_16
    cases assump_5
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        exact assump_23
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p0 p1 p3 p7 p2 p4 p6 : Prop)
theorem file60_93372 : ((((((p6 → False) → (p0 ∧ p2)) ∧ ((False ∧ p1) ∧ (p6 → False))) ∧ (((False → False) ∨ (True ∨ True)) ∨ ((p6 → False) → False))) ∧ ((((p7 ∨ p2) ∧ (p7 → p3)) → False) ∨ (((p4 → False) → False) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply False.elim assump_18


variable (p1 p2 p4 p6 p7 p0 p5 p3 : Prop)
theorem file60_94017 : (((((p1 → False) ∧ (p3 ∧ p6)) ∨ ((p4 → p7) ∨ (p2 → p3))) ∧ (((p4 ∨ False) ∨ (False ∨ True)) → ((p5 → p5) → False))) → ((((p6 ∧ False) ∧ (False ∧ p0)) ∧ ((p6 → p2) ∧ (p3 → p6))) ∨ (((False → False) ∧ (p5 ∧ True)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply Or.inr
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_20
            case intro assump_23 assump_24 =>
              have assump_91 : ((p4 ∨ False) ∨ (False ∨ True)) := by
                apply Or.inr
                apply Or.inr
                apply True.intro
              let assump_31 := assump_3 assump_91
              have assump_92 : (p5 → p5) := by
                intro assump_33
                exact assump_33
              let assump_32 := assump_31 assump_92
              apply False.elim assump_32
    case inr assump_5 =>
      cases assump_5
      case inl assump_39 =>
        apply Or.inr
        intro assump_45
        cases assump_45
        case intro assump_46 assump_47 =>
          cases assump_47
          case intro assump_50 assump_51 =>
            have assump_93 : ((p4 ∨ False) ∨ (False ∨ True)) := by
              apply Or.inr
              apply Or.inr
              apply True.intro
            let assump_58 := assump_3 assump_93
            have assump_94 : (p5 → p5) := by
              intro assump_60
              exact assump_60
            let assump_59 := assump_58 assump_94
            apply False.elim assump_59
      case inr assump_40 =>
        apply Or.inr
        intro assump_70
        cases assump_70
        case intro assump_71 assump_72 =>
          cases assump_72
          case intro assump_75 assump_76 =>
            have assump_95 : ((p4 ∨ False) ∨ (False ∨ True)) := by
              apply Or.inr
              apply Or.inr
              apply True.intro
            let assump_83 := assump_3 assump_95
            have assump_96 : (p5 → p5) := by
              intro assump_85
              exact assump_85
            let assump_84 := assump_83 assump_96
            apply False.elim assump_84


variable (p3 p6 : Prop)
theorem file60_96386 : (((((False ∧ p3) → False) ∨ ((p3 → False) → (False ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_13 : (((False ∧ p3) → False) ∨ ((p3 → False) → (False ∨ p6))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p1 p3 p2 : Prop)
theorem file60_96810 : ((((((True → False) ∧ (p1 → False)) ∧ ((p5 → False) ∨ (p3 → p2))) → (((False → False) → False) → ((False → False) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((True → False) ∧ (p1 → False)) ∧ ((p5 → False) ∨ (p3 → p2))) → (((False → False) → False) → ((False → False) → (False → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p7 p6 p4 p0 p1 p5 : Prop)
theorem file60_97378 : (((((p6 ∨ True) ∧ (False ∧ True)) → ((p1 → p4) ∧ (p5 → p1))) ∨ (((p2 → False) ∧ (p0 → True)) → ((p2 ∨ p1) ∨ (p6 ∧ p5)))) ∨ ((((p0 → p0) → False) → ((p0 ∧ p7) → (p2 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    case inr assump_8 =>
      cases assump_6
      case intro assump_17 assump_18 =>
        apply False.elim assump_17
  intro assump_21
  cases assump_1
  case intro assump_24 assump_25 =>
    cases assump_24
    case inl assump_26 =>
      cases assump_25
      case intro assump_30 assump_31 =>
        apply False.elim assump_30
    case inr assump_27 =>
      cases assump_25
      case intro assump_36 assump_37 =>
        apply False.elim assump_36


variable (p6 p7 p3 p1 p0 p2 p5 : Prop)
theorem file60_98363 : ((((((p6 → p0) → False) → ((p6 → p2) ∧ (p7 → p3))) → (((p5 → p7) → False) ∧ ((p5 → p7) → False))) ∧ ((((False → p6) ∨ (p0 → False)) ∨ ((p1 → True) ∧ (p7 → p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((False → p6) ∨ (p0 → False)) ∨ ((p1 → True) ∧ (p7 → p6))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p0 p3 : Prop)
theorem file60_98915 : (((((True → False) → False) → False) → (((p3 → False) → False) ∨ ((p3 → True) → False))) ∨ ((((p0 → False) ∧ (False → False)) → ((True ∨ p6) → (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_19 : ((True → False) → False) := by
    intro assump_9
    have assump_20 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p5 p4 p2 p1 p7 : Prop)
theorem file60_99470 : (((((p5 ∨ p1) ∧ (False ∨ p1)) ∨ ((True → False) → False)) ∨ (((p4 → False) ∧ (False → p2)) ∨ ((True ∨ p7) ∨ (False ∨ False)))) ∨ ((((p4 ∨ False) → False) → False) ∧ (((p4 → False) ∨ (False ∨ p7)) ∧ ((p4 ∨ p7) → (False → True))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p0 p2 p5 p3 p4 p1 : Prop)
theorem file60_99945 : (((((p4 → False) ∧ (False → False)) ∨ ((False → False) → (p0 → False))) → (((False → False) ∧ (True ∨ True)) ∨ ((p1 ∧ p4) → False))) ∧ ((((False ∧ p1) ∧ (p5 ∧ p7)) ∧ ((p4 ∨ p2) ∧ (False → p3))) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply And.intro
      intro assump_10
      apply False.elim assump_10
      apply Or.inl
      apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_15
    apply False.elim assump_15
    apply Or.inl
    apply True.intro
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        apply False.elim assump_23


variable (p5 p3 p0 p4 p1 p6 : Prop)
theorem file60_100859 : (((((p4 ∧ p1) → (p5 ∨ p4)) → False) → False) ∨ ((((p5 ∨ p6) ∧ (p3 → False)) → ((p0 → True) ∨ (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p4 ∧ p1) → (p5 ∨ p4)) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      exact assump_6
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p5 p7 p2 p0 p1 p3 : Prop)
theorem file60_101306 : (((((p2 → False) → (p7 ∨ p7)) ∧ ((p3 ∧ p3) → (False ∨ p5))) → (((p6 → False) ∨ (p0 ∨ True)) ∨ ((p7 → False) → False))) → ((((p2 ∧ p6) → (p6 → p0)) ∧ ((p1 ∧ False) ∧ (p3 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10


variable (p1 p4 p0 p2 p3 p5 p6 : Prop)
theorem file60_101800 : ((((((p1 ∧ p0) → False) → ((p3 ∨ p6) → False)) ∨ (((p4 → p3) → False) ∧ ((p3 → p2) → False))) ∧ ((((p3 ∧ p4) → (False → p3)) ∨ ((p5 ∧ True) → (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_34 : (((p3 ∧ p4) → (False → p3)) ∨ ((p5 ∧ True) → (p5 → False))) := by
        apply Or.inl
        intro assump_11
        intro assump_12
        apply False.elim assump_12
      let assump_10 := assump_3 assump_34
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        have assump_35 : (((p3 ∧ p4) → (False → p3)) ∨ ((p5 ∧ True) → (p5 → False))) := by
          apply Or.inl
          intro assump_27
          intro assump_28
          apply False.elim assump_28
        let assump_26 := assump_3 assump_35
        apply False.elim assump_26


variable (p2 p5 p0 p3 p6 p1 p4 : Prop)
theorem file60_102793 : ((((((p4 → False) ∨ (p6 ∧ True)) ∨ ((p3 → p2) → False)) → (((p6 ∨ p1) ∨ (p0 → True)) ∧ ((p5 ∧ p3) → (True → True)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p4 → False) ∨ (p6 ∧ True)) ∨ ((p3 → p2) → False)) → (((p6 ∨ p1) ∨ (p0 → True)) ∧ ((p5 ∧ p3) → (True → True)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        intro assump_12
        apply True.intro
      case inr assump_9 =>
        cases assump_9
        case intro assump_13 assump_14 =>
          apply Or.inl
          apply Or.inl
          exact assump_13
    case inr assump_7 =>
      apply Or.inr
      intro assump_21
      apply True.intro
    intro assump_22
    intro assump_23
    apply True.intro
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p6 p0 p7 p3 p5 p1 p4 p2 : Prop)
theorem file60_103737 : (((((p0 ∨ p6) → (p6 → p2)) ∧ ((p3 → False) ∨ (p4 → False))) → False) → ((((False ∧ p5) ∧ (p1 → False)) ∨ ((False → True) ∨ (p3 → False))) ∨ (((True ∨ p1) ∧ (p4 ∨ p3)) ∧ ((p7 ∨ True) ∨ (p0 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p6 p7 p5 p4 p1 p2 p3 p0 : Prop)
theorem file60_104105 : (((((p7 → p6) ∧ (p3 → False)) ∨ ((p4 → True) ∨ (False ∧ p6))) ∨ (((p5 ∧ p4) → False) → False)) → ((((p3 ∨ p0) ∧ (p6 ∧ p0)) ∨ ((True → False) → False)) ∨ (((p6 ∧ p6) ∧ (p4 ∧ p3)) ∨ ((p2 ∧ p1) ∧ (False → False))))) := by
  intro assump_42
  cases assump_42
  case inl assump_43 =>
    cases assump_43
    case inl assump_45 =>
      cases assump_45
      case intro assump_47 assump_48 =>
        apply Or.inl
        apply Or.inr
        intro assump_53
        have assump_84 : True := by
          apply True.intro
        let assump_56 := assump_53 assump_84
        apply False.elim assump_56
    case inr assump_46 =>
      cases assump_46
      case inl assump_60 =>
        apply Or.inl
        apply Or.inr
        intro assump_64
        have assump_85 : True := by
          apply True.intro
        let assump_67 := assump_64 assump_85
        apply False.elim assump_67
      case inr assump_61 =>
        cases assump_61
        case intro assump_71 assump_72 =>
          apply False.elim assump_71
  case inr assump_44 =>
    apply Or.inl
    apply Or.inr
    intro assump_77
    have assump_86 : True := by
      apply True.intro
    let assump_80 := assump_77 assump_86
    apply False.elim assump_80


variable (p7 p1 p6 p5 p4 p0 : Prop)
theorem file60_105382 : (((((p7 ∨ p4) → (p0 → False)) ∧ ((p0 ∨ p1) ∧ (True → False))) → False) ∨ ((((p1 → p0) ∨ (p1 → p1)) ∧ ((p0 → p6) → False)) ∧ (((p7 ∨ p5) → (False → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_26 : True := by
          apply True.intro
        let assump_14 := assump_7 assump_26
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_27 : True := by
          apply True.intro
        let assump_22 := assump_7 assump_27
        apply False.elim assump_22


variable (p5 p3 p0 p1 p2 p6 : Prop)
theorem file60_106111 : (((((p1 → False) ∨ (p6 → False)) → ((True ∨ p6) ∨ (p3 ∨ p3))) ∨ (((p0 → False) ∧ (False → False)) ∨ ((p6 → True) → False))) ∨ ((((p6 → False) → False) ∨ ((p6 → False) → False)) ∨ (((p6 ∧ p1) ∧ (p2 ∧ p5)) ∨ ((False → False) ∧ (False → p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_11 =>
    apply Or.inl
    apply Or.inl
    apply True.intro


variable (p7 p1 p3 p0 p2 p4 p5 : Prop)
theorem file60_106644 : (((((p5 ∨ p7) ∨ (p0 → False)) ∧ ((p3 → False) ∧ (p3 → False))) ∧ (((False → False) → False) ∧ ((p0 ∧ p4) ∨ (p1 ∧ p2)))) → False) := by
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
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  have assump_142 : (False → False) := by
                    intro assump_33
                    apply False.elim assump_33
                  let assump_32 := assump_18 assump_142
                  apply False.elim assump_32
              case inr assump_23 =>
                cases assump_23
                case intro assump_39 assump_40 =>
                  have assump_143 : (False → False) := by
                    intro assump_48
                    apply False.elim assump_48
                  let assump_47 := assump_18 assump_143
                  apply False.elim assump_47
        case inr assump_9 =>
          cases assump_5
          case intro assump_56 assump_57 =>
            cases assump_3
            case intro assump_62 assump_63 =>
              cases assump_63
              case inl assump_66 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  have assump_144 : (False → False) := by
                    intro assump_77
                    apply False.elim assump_77
                  let assump_76 := assump_62 assump_144
                  apply False.elim assump_76
              case inr assump_67 =>
                cases assump_67
                case intro assump_83 assump_84 =>
                  have assump_145 : (False → False) := by
                    intro assump_92
                    apply False.elim assump_92
                  let assump_91 := assump_62 assump_145
                  apply False.elim assump_91
      case inr assump_7 =>
        cases assump_5
        case intro assump_100 assump_101 =>
          cases assump_3
          case intro assump_106 assump_107 =>
            cases assump_107
            case inl assump_110 =>
              cases assump_110
              case intro assump_112 assump_113 =>
                have assump_146 : (False → False) := by
                  intro assump_121
                  apply False.elim assump_121
                let assump_120 := assump_106 assump_146
                apply False.elim assump_120
            case inr assump_111 =>
              cases assump_111
              case intro assump_127 assump_128 =>
                have assump_147 : (False → False) := by
                  intro assump_136
                  apply False.elim assump_136
                let assump_135 := assump_106 assump_147
                apply False.elim assump_135


variable (p3 p5 p2 p0 p4 p1 p7 : Prop)
theorem file60_109778 : (((((p4 ∧ p0) → (False → p7)) → ((True ∨ False) ∧ (p1 → False))) ∨ (((False ∧ p5) → False) → ((p2 → p5) ∧ (p2 → False)))) → ((((p1 → False) → False) → ((p5 ∧ p1) ∧ (p2 → False))) → (((p3 ∧ False) → (p1 → False)) ∨ ((p4 ∨ False) ∧ (False → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  case inr assump_6 =>
    apply Or.inl
    intro assump_21
    intro assump_22
    cases assump_21
    case intro assump_25 assump_26 =>
      apply False.elim assump_26


variable (p0 p4 p5 p6 p3 p7 p2 : Prop)
theorem file60_110488 : (((((p4 ∨ p2) → False) ∧ ((p7 → False) ∧ (p2 ∧ p4))) ∧ (((p5 → True) ∨ (p6 ∧ p0)) → False)) → ((((p2 → p0) ∨ (p3 ∧ p2)) → False) ∧ (((p3 ∨ p6) ∨ (p2 ∨ p4)) ∧ ((p6 → False) → (p3 ∧ p6))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            have assump_128 : ((p5 → True) ∨ (p6 ∧ p0)) := by
              apply Or.inl
              intro assump_26
              apply True.intro
            let assump_25 := assump_8 assump_128
            apply False.elim assump_25
  case inr assump_4 =>
    cases assump_4
    case intro assump_30 assump_31 =>
      cases assump_1
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_39
          case intro assump_42 assump_43 =>
            cases assump_43
            case intro assump_46 assump_47 =>
              have assump_129 : ((p5 → True) ∨ (p6 ∧ p0)) := by
                apply Or.inl
                intro assump_55
                apply True.intro
              let assump_54 := assump_37 assump_129
              apply False.elim assump_54
  apply And.intro
  cases assump_1
  case intro assump_59 assump_60 =>
    cases assump_59
    case intro assump_61 assump_62 =>
      cases assump_62
      case intro assump_65 assump_66 =>
        cases assump_66
        case intro assump_69 assump_70 =>
          apply Or.inr
          apply Or.inl
          exact assump_69
  intro assump_77
  apply And.intro
  cases assump_1
  case intro assump_80 assump_81 =>
    cases assump_80
    case intro assump_82 assump_83 =>
      cases assump_83
      case intro assump_86 assump_87 =>
        cases assump_87
        case intro assump_90 assump_91 =>
          have assump_130 : ((p5 → True) ∨ (p6 ∧ p0)) := by
            apply Or.inl
            intro assump_99
            apply True.intro
          let assump_98 := assump_81 assump_130
          apply False.elim assump_98
  cases assump_1
  case intro assump_105 assump_106 =>
    cases assump_105
    case intro assump_107 assump_108 =>
      cases assump_108
      case intro assump_111 assump_112 =>
        cases assump_112
        case intro assump_115 assump_116 =>
          have assump_131 : ((p5 → True) ∨ (p6 ∧ p0)) := by
            apply Or.inl
            intro assump_124
            apply True.intro
          let assump_123 := assump_106 assump_131
          apply False.elim assump_123


variable (p5 p0 p1 p7 p4 p6 p2 : Prop)
theorem file60_113240 : (((((p1 ∧ False) ∨ (p5 → False)) → ((True ∨ False) ∨ (p6 ∧ p4))) → False) → ((((False → False) → (p2 → False)) → ((p2 → False) ∨ (p1 → False))) ∧ (((p4 ∨ p7) → (p7 ∨ p4)) ∧ ((True ∧ p0) ∧ (True → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_74 : (((p1 ∧ False) ∨ (p5 → False)) → ((True ∨ False) ∨ (p6 ∧ p4))) := by
    intro assump_12
    cases assump_12
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
    case inr assump_14 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_11 := assump_1 assump_74
  apply False.elim assump_11
  apply And.intro
  intro assump_26
  cases assump_26
  case inl assump_27 =>
    apply Or.inr
    exact assump_27
  case inr assump_28 =>
    apply Or.inl
    exact assump_28
  apply And.intro
  apply And.intro
  apply True.intro
  have assump_75 : (((p1 ∧ False) ∨ (p5 → False)) → ((True ∨ False) ∨ (p6 ∧ p4))) := by
    intro assump_40
    cases assump_40
    case inl assump_41 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        apply False.elim assump_44
    case inr assump_42 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_39 := assump_1 assump_75
  apply False.elim assump_39
  intro assump_54
  have assump_76 : (((p1 ∧ False) ∨ (p5 → False)) → ((True ∨ False) ∨ (p6 ∧ p4))) := by
    intro assump_60
    cases assump_60
    case inl assump_61 =>
      cases assump_61
      case intro assump_63 assump_64 =>
        apply False.elim assump_64
    case inr assump_62 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_59 := assump_1 assump_76
  apply False.elim assump_59


variable (p5 p6 p0 p1 p7 p3 p4 : Prop)
theorem file60_115064 : (((((p7 ∨ p5) ∨ (p5 ∨ p6)) ∧ ((p0 → False) ∧ (p0 → False))) → (((p4 → p6) → (False → False)) ∨ ((p3 → False) ∨ (p1 → False)))) ∨ ((((p0 → False) ∧ (p4 → p1)) → ((p6 → p3) → False)) ∧ (((p4 ∨ True) → False) → False))) := by
  apply Or.inl
  intro assump_27
  cases assump_27
  case intro assump_28 assump_29 =>
    cases assump_28
    case inl assump_30 =>
      cases assump_30
      case inl assump_32 =>
        cases assump_29
        case intro assump_36 assump_37 =>
          apply Or.inl
          intro assump_42
          intro assump_43
          apply False.elim assump_43
      case inr assump_33 =>
        cases assump_29
        case intro assump_48 assump_49 =>
          apply Or.inl
          intro assump_54
          intro assump_55
          apply False.elim assump_55
    case inr assump_31 =>
      cases assump_31
      case inl assump_58 =>
        cases assump_29
        case intro assump_62 assump_63 =>
          apply Or.inl
          intro assump_68
          intro assump_69
          apply False.elim assump_69
      case inr assump_59 =>
        cases assump_29
        case intro assump_74 assump_75 =>
          apply Or.inl
          intro assump_80
          intro assump_81
          apply False.elim assump_81


variable (p0 p3 p7 p4 p2 p1 p5 : Prop)
theorem file60_116377 : (((((p0 → False) ∧ (False → False)) → ((True → False) → False)) ∧ (((p2 → False) ∨ (p0 → False)) ∧ ((p7 → False) → (p3 ∧ p5)))) → ((((p3 ∧ p2) ∨ (p7 ∧ p4)) ∧ ((p1 ∧ p1) ∧ (p0 ∨ p3))) → (((p5 ∧ p2) ∧ (False ∧ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        apply False.elim assump_12


variable (p7 p4 p0 p6 p3 p2 : Prop)
theorem file60_116920 : ((((((p2 ∨ True) ∧ (True ∧ True)) → False) → (((p4 → False) ∧ (p6 → False)) → ((False ∧ p3) ∨ (p0 ∨ p7)))) → False) → False) := by
  intro assump_38
  have assump_59 : ((((p2 ∨ True) ∧ (True ∧ True)) → False) → (((p4 → False) ∧ (p6 → False)) → ((False ∧ p3) ∨ (p0 ∨ p7)))) := by
    intro assump_42
    intro assump_43
    cases assump_43
    case intro assump_44 assump_45 =>
      have assump_60 : ((p2 ∨ True) ∧ (True ∧ True)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_52 := assump_42 assump_60
      apply False.elim assump_52
  let assump_41 := assump_38 assump_59
  apply False.elim assump_41


variable (p7 p3 p2 p1 p4 p5 p0 : Prop)
theorem file60_117707 : ((((((p1 → False) ∨ (p5 ∨ p0)) ∨ ((p3 ∨ p4) → False)) → False) ∧ ((((p0 ∧ False) → (p1 → p5)) ∨ ((p2 ∨ p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((p0 ∧ False) → (p1 → p5)) ∨ ((p2 ∨ p7) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p1 p0 p2 p3 p5 p6 : Prop)
theorem file60_118282 : ((((((p5 → p0) ∨ (p5 → p2)) ∧ ((p1 → p2) → False)) → False) ∧ ((((p3 ∨ False) ∨ (p1 → p0)) → ((p0 ∧ p5) ∧ (True ∧ p6))) ∧ (((False → p2) ∨ (True ∨ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((False → p2) ∨ (True ∨ p3)) := by
        apply Or.inl
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p2 p7 p6 p4 p5 : Prop)
theorem file60_118853 : (((((p4 ∨ p2) → False) → False) → False) → ((((False → p5) ∧ (p7 ∨ p6)) → False) → (((p6 ∨ p4) → (p2 → False)) ∧ ((p2 → False) ∨ (p7 → p2))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    have assump_62 : (((p4 ∨ p2) → False) → False) := by
      intro assump_16
      have assump_63 : (p4 ∨ p2) := by
        apply Or.inr
        exact assump_4
      let assump_19 := assump_16 assump_63
      apply False.elim assump_19
    let assump_15 := assump_1 assump_62
    apply False.elim assump_15
  case inr assump_8 =>
    have assump_64 : (((p4 ∨ p2) → False) → False) := by
      intro assump_33
      have assump_65 : (p4 ∨ p2) := by
        apply Or.inl
        exact assump_8
      let assump_36 := assump_33 assump_65
      apply False.elim assump_36
    let assump_32 := assump_1 assump_64
    apply False.elim assump_32
  apply Or.inl
  intro assump_47
  have assump_66 : (((p4 ∨ p2) → False) → False) := by
    intro assump_52
    have assump_67 : (p4 ∨ p2) := by
      apply Or.inr
      exact assump_47
    let assump_55 := assump_52 assump_67
    apply False.elim assump_55
  let assump_51 := assump_1 assump_66
  apply False.elim assump_51


variable (p2 p0 p1 p5 p4 p6 p3 : Prop)
theorem file60_120157 : (((((p1 → False) ∧ (p0 ∨ p6)) → False) → False) → ((((p5 → False) ∧ (p2 ∧ False)) → False) ∧ (((p4 → False) ∧ (True ∧ p2)) → ((p0 ∧ False) → (p3 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  intro assump_13
  intro assump_14
  intro assump_15
  cases assump_14
  case intro assump_18 assump_19 =>
    apply False.elim assump_19


variable (p5 p3 p4 p7 p1 p6 p0 : Prop)
theorem file60_120713 : (((((p6 → p3) ∨ (p0 ∨ p7)) → ((p5 → False) ∨ (p4 → p5))) ∧ (((p6 ∧ p1) ∨ (True ∧ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((p6 ∧ p1) ∨ (True ∧ True)) := by
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p1 p2 p5 p4 p6 p0 : Prop)
theorem file60_121165 : ((((((p5 ∧ p1) ∧ (p1 → False)) ∨ ((True ∧ p4) → (p4 ∨ p1))) ∨ (((p0 ∨ p6) → (p6 → False)) → ((p0 → p2) ∨ (p5 ∧ p5)))) → False) → False) := by
  intro assump_9
  have assump_23 : ((((p5 ∧ p1) ∧ (p1 → False)) ∨ ((True ∧ p4) → (p4 ∨ p1))) ∨ (((p0 ∨ p6) → (p6 → False)) → ((p0 → p2) ∨ (p5 ∧ p5)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply Or.inl
      exact assump_15
  let assump_12 := assump_9 assump_23
  apply False.elim assump_12


variable (p0 p4 p6 p1 p2 p7 p5 : Prop)
theorem file60_121748 : ((((((p5 → False) → (p4 ∧ True)) → ((False → False) ∨ (False ∨ p1))) ∨ (((p4 → p0) ∧ (p1 ∧ p0)) ∧ ((p7 ∧ p7) → False))) → ((((False → p0) ∧ (p6 → p6)) ∨ ((True ∨ True) → (p2 → p7))) → False)) → False) := by
  intro assump_9
  have assump_29 : ((((p5 → False) → (p4 ∧ True)) → ((False → False) ∨ (False ∨ p1))) ∨ (((p4 → p0) ∧ (p1 ∧ p0)) ∧ ((p7 ∧ p7) → False))) := by
    apply Or.inl
    intro assump_13
    apply Or.inl
    intro assump_16
    apply False.elim assump_16
  let assump_12 := assump_9 assump_29
  have assump_30 : (((False → p0) ∧ (p6 → p6)) ∨ ((True ∨ True) → (p2 → p7))) := by
    apply Or.inl
    apply And.intro
    intro assump_20
    apply False.elim assump_20
    intro assump_23
    exact assump_23
  let assump_19 := assump_12 assump_30
  apply False.elim assump_19


