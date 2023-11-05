variable (p1 p0 p3 p7 p4 p5 : Prop)
theorem file44_44 : (((((p5 ∧ p1) ∨ (p1 → p7)) → False) → (((True → False) → False) → False)) → ((((p5 ∧ p4) ∨ (False → False)) ∨ ((p4 → p5) ∧ (p7 ∨ p0))) ∨ (((p4 ∧ True) ∨ (p7 ∨ p3)) ∧ ((p5 ∧ p0) → (p5 → True))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p7 p4 p5 p2 p0 p3 p1 : Prop)
theorem file44_415 : ((((((p3 ∧ p4) → (p0 → p2)) ∨ ((True → True) → (True ∨ True))) ∨ (((p1 ∨ p5) → False) → False)) ∧ ((((p5 → False) → False) ∧ ((p7 → p0) ∨ (p0 → False))) ∧ (((p2 → True) ∨ (p7 → False)) → False))) → False) := by
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
          case intro assump_20 assump_21 =>
            cases assump_21
            case inl assump_24 =>
              have assump_100 : ((p2 → True) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_31
                apply True.intro
              let assump_30 := assump_19 assump_100
              apply False.elim assump_30
            case inr assump_25 =>
              have assump_101 : ((p2 → True) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_40
                apply True.intro
              let assump_39 := assump_19 assump_101
              apply False.elim assump_39
      case inr assump_15 =>
        cases assump_11
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_49
            case inl assump_52 =>
              have assump_102 : ((p2 → True) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_59
                apply True.intro
              let assump_58 := assump_47 assump_102
              apply False.elim assump_58
            case inr assump_53 =>
              have assump_103 : ((p2 → True) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_68
                apply True.intro
              let assump_67 := assump_47 assump_103
              apply False.elim assump_67
    case inr assump_13 =>
      cases assump_11
      case intro assump_74 assump_75 =>
        cases assump_74
        case intro assump_76 assump_77 =>
          cases assump_77
          case inl assump_80 =>
            have assump_104 : ((p2 → True) ∨ (p7 → False)) := by
              apply Or.inl
              intro assump_87
              apply True.intro
            let assump_86 := assump_75 assump_104
            apply False.elim assump_86
          case inr assump_81 =>
            have assump_105 : ((p2 → True) ∨ (p7 → False)) := by
              apply Or.inl
              intro assump_96
              apply True.intro
            let assump_95 := assump_75 assump_105
            apply False.elim assump_95


variable (p1 p6 p5 p4 p0 : Prop)
theorem file44_3085 : ((((((p4 → p1) ∧ (p0 → True)) ∨ ((p4 ∨ p4) → (p4 → False))) ∧ (((p6 ∧ p6) → False) ∧ ((False ∨ p6) → False))) ∧ ((((True ∨ p5) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            have assump_54 : (((True ∨ p5) → False) → False) := by
              intro assump_23
              have assump_55 : (True ∨ p5) := by
                apply Or.inl
                apply True.intro
              let assump_26 := assump_23 assump_55
              apply False.elim assump_26
            let assump_22 := assump_3 assump_54
            apply False.elim assump_22
      case inr assump_7 =>
        cases assump_5
        case intro assump_35 assump_36 =>
          have assump_56 : (((True ∨ p5) → False) → False) := by
            intro assump_44
            have assump_57 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_47 := assump_44 assump_57
            apply False.elim assump_47
          let assump_43 := assump_3 assump_56
          apply False.elim assump_43


variable (p7 p0 p3 : Prop)
theorem file44_4457 : ((((((p3 ∧ p0) ∨ (p3 ∧ p7)) ∧ ((p0 → p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p3 ∧ p0) ∨ (p3 ∧ p7)) ∧ ((p0 → p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_44 : (p0 → p3) := by
            intro assump_19
            exact assump_10
          let assump_18 := assump_7 assump_44
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_25 assump_26 =>
          have assump_45 : (p0 → p3) := by
            intro assump_34
            exact assump_25
          let assump_33 := assump_7 assump_45
          apply False.elim assump_33
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p0 p2 : Prop)
theorem file44_5397 : ((((((p0 ∧ p2) → (False → p0)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p0 ∧ p2) → (False → p0)) → False) → False) := by
    intro assump_5
    have assump_20 : ((p0 ∧ p2) → (False → p0)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p0 p2 p1 p4 p6 p3 : Prop)
theorem file44_5902 : ((((((True → True) ∧ (p4 ∨ False)) ∧ ((p3 ∧ p4) → (p0 ∧ p6))) ∧ (((p3 ∨ p1) → (p2 → False)) → False)) ∧ ((((p2 → True) ∧ (p4 → False)) → ((True ∧ p0) → (p3 → True))) → False)) → False) := by
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
          case inl assump_12 =>
            have assump_31 : (((p2 → True) ∧ (p4 → False)) → ((True ∧ p0) → (p3 → True))) := by
              intro assump_23
              intro assump_24
              intro assump_25
              apply True.intro
            let assump_22 := assump_3 assump_31
            apply False.elim assump_22
          case inr assump_13 =>
            apply False.elim assump_13


variable (p6 p3 p1 p4 p0 p2 p5 : Prop)
theorem file44_6833 : (((((p3 ∨ p1) → (p2 ∧ p3)) ∧ ((p2 ∧ p4) → (p2 → p2))) ∨ (((p2 → False) ∨ (p5 → False)) → False)) → ((((p0 → True) → False) → ((p5 → p3) ∨ (p0 → p1))) ∨ (((False ∧ p1) ∨ (False → True)) → ((p6 ∧ p2) ∧ (p0 ∧ p1))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      apply Or.inl
      intro assump_13
      have assump_36 : (p0 → True) := by
        intro assump_18
        apply True.intro
      let assump_17 := assump_10 assump_36
      apply False.elim assump_17
  case inr assump_3 =>
    apply Or.inl
    intro assump_24
    apply Or.inl
    intro assump_27
    have assump_37 : (p0 → True) := by
      intro assump_32
      apply True.intro
    let assump_31 := assump_24 assump_37
    apply False.elim assump_31


variable (p6 p5 p4 p7 p0 p3 p2 : Prop)
theorem file44_7729 : (((((p7 ∧ p2) ∨ (p7 ∨ False)) → False) ∧ (((False → p4) ∨ (p3 → False)) ∨ ((p4 ∨ p4) ∨ (p7 → False)))) → ((((p6 ∧ True) → (p7 → False)) ∨ ((True ∧ p5) → (p3 → False))) ∧ (((True → False) → False) ∨ ((True ∧ p0) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        cases assump_12
        case intro assump_16 assump_17 =>
          have assump_165 : ((p7 ∧ p2) ∨ (p7 ∨ False)) := by
            apply Or.inr
            apply Or.inl
            exact assump_13
          let assump_25 := assump_2 assump_165
          apply False.elim assump_25
      case inr assump_9 =>
        apply Or.inl
        intro assump_31
        intro assump_32
        cases assump_31
        case intro assump_35 assump_36 =>
          have assump_166 : ((p7 ∧ p2) ∨ (p7 ∨ False)) := by
            apply Or.inr
            apply Or.inl
            exact assump_32
          let assump_44 := assump_2 assump_166
          apply False.elim assump_44
    case inr assump_7 =>
      cases assump_7
      case inl assump_48 =>
        cases assump_48
        case inl assump_50 =>
          apply Or.inl
          intro assump_54
          intro assump_55
          cases assump_54
          case intro assump_58 assump_59 =>
            have assump_167 : ((p7 ∧ p2) ∨ (p7 ∨ False)) := by
              apply Or.inr
              apply Or.inl
              exact assump_55
            let assump_67 := assump_2 assump_167
            apply False.elim assump_67
        case inr assump_51 =>
          apply Or.inl
          intro assump_73
          intro assump_74
          cases assump_73
          case intro assump_77 assump_78 =>
            have assump_168 : ((p7 ∧ p2) ∨ (p7 ∨ False)) := by
              apply Or.inr
              apply Or.inl
              exact assump_74
            let assump_86 := assump_2 assump_168
            apply False.elim assump_86
      case inr assump_49 =>
        apply Or.inl
        intro assump_92
        intro assump_93
        cases assump_92
        case intro assump_96 assump_97 =>
          have assump_169 : p7 := by
            exact assump_93
          let assump_104 := assump_49 assump_169
          apply False.elim assump_104
  cases assump_1
  case intro assump_108 assump_109 =>
    cases assump_109
    case inl assump_112 =>
      cases assump_112
      case inl assump_114 =>
        apply Or.inl
        intro assump_118
        have assump_170 : True := by
          apply True.intro
        let assump_121 := assump_118 assump_170
        apply False.elim assump_121
      case inr assump_115 =>
        apply Or.inl
        intro assump_127
        have assump_171 : True := by
          apply True.intro
        let assump_130 := assump_127 assump_171
        apply False.elim assump_130
    case inr assump_113 =>
      cases assump_113
      case inl assump_134 =>
        cases assump_134
        case inl assump_136 =>
          apply Or.inl
          intro assump_140
          have assump_172 : True := by
            apply True.intro
          let assump_143 := assump_140 assump_172
          apply False.elim assump_143
        case inr assump_137 =>
          apply Or.inl
          intro assump_149
          have assump_173 : True := by
            apply True.intro
          let assump_152 := assump_149 assump_173
          apply False.elim assump_152
      case inr assump_135 =>
        apply Or.inl
        intro assump_158
        have assump_174 : True := by
          apply True.intro
        let assump_161 := assump_158 assump_174
        apply False.elim assump_161


variable (p5 p6 p3 p4 p2 p1 p0 : Prop)
theorem file44_11548 : ((((((p0 → p0) → False) ∧ ((p6 ∨ p1) ∧ (False ∧ p2))) → (((p0 → False) → (p4 ∧ False)) → ((p6 → p5) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p0 → p0) → False) ∧ ((p6 ∨ p1) ∧ (False ∧ p2))) → (((p0 → False) → (p4 ∧ False)) → ((p6 → p5) ∨ (p3 → False)))) := by
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
            apply False.elim assump_19
        case inr assump_16 =>
          cases assump_14
          case intro assump_25 assump_26 =>
            apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 p6 p4 p7 p2 p5 p0 p3 : Prop)
theorem file44_12437 : (((((False ∧ p6) → (True → False)) ∨ ((p2 ∧ p4) ∧ (p4 ∧ p4))) ∨ (((p6 → False) → (True → p5)) ∧ ((False → p2) ∧ (p7 ∧ p0)))) ∨ ((((p6 ∨ p2) ∧ (p5 ∨ p2)) → ((p3 ∨ p7) → (p0 → p7))) ∨ (((p1 → False) ∧ (p0 ∧ p7)) ∧ ((p5 → False) → (p2 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p5 p1 p0 p7 p4 p6 : Prop)
theorem file44_12908 : (((((p4 → False) ∧ (p4 ∨ False)) → ((p7 ∧ p6) ∧ (p1 → False))) → False) → ((((p1 ∧ True) → (True ∧ p4)) ∨ ((p6 ∨ p6) → (p7 ∨ p6))) → (((True ∨ p4) ∨ (p0 ∧ p5)) → ((p1 ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_2
        case inl assump_17 =>
          have assump_343 : (((p4 → False) ∧ (p4 ∨ False)) → ((p7 ∧ p6) ∧ (p1 → False))) := by
            intro assump_24
            apply And.intro
            apply And.intro
            cases assump_24
            case intro assump_25 assump_26 =>
              cases assump_26
              case inl assump_29 =>
                exact assump_6
              case inr assump_30 =>
                apply False.elim assump_30
            cases assump_24
            case intro assump_35 assump_36 =>
              cases assump_36
              case inl assump_39 =>
                have assump_344 : p4 := by
                  exact assump_39
                let assump_44 := assump_35 assump_344
                apply False.elim assump_44
              case inr assump_40 =>
                apply False.elim assump_40
            intro assump_50
            cases assump_24
            case intro assump_53 assump_54 =>
              cases assump_54
              case inl assump_57 =>
                have assump_345 : p4 := by
                  exact assump_57
                let assump_62 := assump_53 assump_345
                apply False.elim assump_62
              case inr assump_58 =>
                apply False.elim assump_58
          let assump_23 := assump_1 assump_343
          apply False.elim assump_23
        case inr assump_18 =>
          have assump_346 : (((p4 → False) ∧ (p4 ∨ False)) → ((p7 ∧ p6) ∧ (p1 → False))) := by
            intro assump_76
            apply And.intro
            apply And.intro
            cases assump_76
            case intro assump_77 assump_78 =>
              cases assump_78
              case inl assump_81 =>
                exact assump_6
              case inr assump_82 =>
                apply False.elim assump_82
            cases assump_76
            case intro assump_87 assump_88 =>
              cases assump_88
              case inl assump_91 =>
                have assump_347 : p4 := by
                  exact assump_91
                let assump_96 := assump_87 assump_347
                apply False.elim assump_96
              case inr assump_92 =>
                apply False.elim assump_92
            intro assump_102
            cases assump_76
            case intro assump_105 assump_106 =>
              cases assump_106
              case inl assump_109 =>
                have assump_348 : p4 := by
                  exact assump_109
                let assump_114 := assump_105 assump_348
                apply False.elim assump_114
              case inr assump_110 =>
                apply False.elim assump_110
          let assump_75 := assump_1 assump_346
          apply False.elim assump_75
      case inr assump_14 =>
        cases assump_2
        case inl assump_125 =>
          have assump_349 : (((p4 → False) ∧ (p4 ∨ False)) → ((p7 ∧ p6) ∧ (p1 → False))) := by
            intro assump_132
            apply And.intro
            apply And.intro
            cases assump_132
            case intro assump_133 assump_134 =>
              cases assump_134
              case inl assump_137 =>
                exact assump_6
              case inr assump_138 =>
                apply False.elim assump_138
            cases assump_132
            case intro assump_143 assump_144 =>
              cases assump_144
              case inl assump_147 =>
                have assump_350 : p4 := by
                  exact assump_147
                let assump_152 := assump_143 assump_350
                apply False.elim assump_152
              case inr assump_148 =>
                apply False.elim assump_148
            intro assump_158
            cases assump_132
            case intro assump_161 assump_162 =>
              cases assump_162
              case inl assump_165 =>
                have assump_351 : p4 := by
                  exact assump_165
                let assump_170 := assump_161 assump_351
                apply False.elim assump_170
              case inr assump_166 =>
                apply False.elim assump_166
          let assump_131 := assump_1 assump_349
          apply False.elim assump_131
        case inr assump_126 =>
          have assump_352 : (((p4 → False) ∧ (p4 ∨ False)) → ((p7 ∧ p6) ∧ (p1 → False))) := by
            intro assump_184
            apply And.intro
            apply And.intro
            cases assump_184
            case intro assump_185 assump_186 =>
              cases assump_186
              case inl assump_189 =>
                exact assump_6
              case inr assump_190 =>
                apply False.elim assump_190
            cases assump_184
            case intro assump_195 assump_196 =>
              cases assump_196
              case inl assump_199 =>
                have assump_353 : p4 := by
                  exact assump_199
                let assump_204 := assump_195 assump_353
                apply False.elim assump_204
              case inr assump_200 =>
                apply False.elim assump_200
            intro assump_210
            cases assump_184
            case intro assump_213 assump_214 =>
              cases assump_214
              case inl assump_217 =>
                have assump_354 : p4 := by
                  exact assump_217
                let assump_222 := assump_213 assump_354
                apply False.elim assump_222
              case inr assump_218 =>
                apply False.elim assump_218
          let assump_183 := assump_1 assump_352
          apply False.elim assump_183
    case inr assump_12 =>
      cases assump_12
      case intro assump_231 assump_232 =>
        cases assump_2
        case inl assump_237 =>
          have assump_355 : (((p4 → False) ∧ (p4 ∨ False)) → ((p7 ∧ p6) ∧ (p1 → False))) := by
            intro assump_244
            apply And.intro
            apply And.intro
            cases assump_244
            case intro assump_245 assump_246 =>
              cases assump_246
              case inl assump_249 =>
                exact assump_6
              case inr assump_250 =>
                apply False.elim assump_250
            cases assump_244
            case intro assump_255 assump_256 =>
              cases assump_256
              case inl assump_259 =>
                have assump_356 : p4 := by
                  exact assump_259
                let assump_264 := assump_255 assump_356
                apply False.elim assump_264
              case inr assump_260 =>
                apply False.elim assump_260
            intro assump_270
            cases assump_244
            case intro assump_273 assump_274 =>
              cases assump_274
              case inl assump_277 =>
                have assump_357 : p4 := by
                  exact assump_277
                let assump_282 := assump_273 assump_357
                apply False.elim assump_282
              case inr assump_278 =>
                apply False.elim assump_278
          let assump_243 := assump_1 assump_355
          apply False.elim assump_243
        case inr assump_238 =>
          have assump_358 : (((p4 → False) ∧ (p4 ∨ False)) → ((p7 ∧ p6) ∧ (p1 → False))) := by
            intro assump_296
            apply And.intro
            apply And.intro
            cases assump_296
            case intro assump_297 assump_298 =>
              cases assump_298
              case inl assump_301 =>
                exact assump_6
              case inr assump_302 =>
                apply False.elim assump_302
            cases assump_296
            case intro assump_307 assump_308 =>
              cases assump_308
              case inl assump_311 =>
                have assump_359 : p4 := by
                  exact assump_311
                let assump_316 := assump_307 assump_359
                apply False.elim assump_316
              case inr assump_312 =>
                apply False.elim assump_312
            intro assump_322
            cases assump_296
            case intro assump_325 assump_326 =>
              cases assump_326
              case inl assump_329 =>
                have assump_360 : p4 := by
                  exact assump_329
                let assump_334 := assump_325 assump_360
                apply False.elim assump_334
              case inr assump_330 =>
                apply False.elim assump_330
          let assump_295 := assump_1 assump_358
          apply False.elim assump_295


variable (p3 p6 p2 p5 p0 p1 p7 p4 : Prop)
theorem file44_21855 : (((((p7 ∧ p7) → (p2 → p0)) → ((p6 → p3) → False)) ∧ (((p3 ∧ p2) ∧ (False ∧ p1)) ∧ ((p4 → p2) ∧ (p4 ∨ p0)))) → ((((p4 ∧ True) → False) → False) ∧ (((p5 → True) ∨ (p6 → p4)) ∧ ((p2 ∨ p5) → (p0 ∧ p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
  apply And.intro
  cases assump_1
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_30
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
  intro assump_41
  apply And.intro
  cases assump_41
  case inl assump_42 =>
    cases assump_1
    case intro assump_46 assump_47 =>
      cases assump_47
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_53
            case intro assump_60 assump_61 =>
              apply False.elim assump_60
  case inr assump_43 =>
    cases assump_1
    case intro assump_66 assump_67 =>
      cases assump_67
      case intro assump_70 assump_71 =>
        cases assump_70
        case intro assump_72 assump_73 =>
          cases assump_72
          case intro assump_74 assump_75 =>
            cases assump_73
            case intro assump_80 assump_81 =>
              apply False.elim assump_80
  cases assump_41
  case inl assump_84 =>
    cases assump_1
    case intro assump_88 assump_89 =>
      cases assump_89
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_94
          case intro assump_96 assump_97 =>
            cases assump_95
            case intro assump_102 assump_103 =>
              apply False.elim assump_102
  case inr assump_85 =>
    cases assump_1
    case intro assump_108 assump_109 =>
      cases assump_109
      case intro assump_112 assump_113 =>
        cases assump_112
        case intro assump_114 assump_115 =>
          cases assump_114
          case intro assump_116 assump_117 =>
            cases assump_115
            case intro assump_122 assump_123 =>
              apply False.elim assump_122


variable (p2 p7 p0 p1 p6 : Prop)
theorem file44_24546 : (((((p0 → False) ∧ (p7 ∨ p2)) → ((False ∧ p7) → False)) → False) → ((((False ∧ p6) ∨ (p6 ∨ False)) → ((p6 ∨ False) ∨ (p1 → False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_17 : (((p0 → False) ∧ (p7 ∨ p2)) → ((False ∧ p7) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_7 := assump_1 assump_17
  apply False.elim assump_7


variable (p3 p1 p5 p0 p6 p2 p4 : Prop)
theorem file44_25063 : (((((p0 ∨ p6) ∨ (False → p5)) → False) → (((p0 → p4) ∨ (True ∨ p3)) ∧ ((p2 ∨ p3) → False))) ∨ ((((p1 ∨ p2) → False) → False) ∧ (((p1 → False) → (False → False)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_37 : ((p0 ∨ p6) ∨ (False → p5)) := by
    apply Or.inl
    apply Or.inl
    exact assump_4
  let assump_8 := assump_1 assump_37
  apply False.elim assump_8
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    have assump_38 : ((p0 ∨ p6) ∨ (False → p5)) := by
      apply Or.inr
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_1 assump_38
    apply False.elim assump_19
  case inr assump_14 =>
    have assump_39 : ((p0 ∨ p6) ∨ (False → p5)) := by
      apply Or.inr
      intro assump_31
      apply False.elim assump_31
    let assump_30 := assump_1 assump_39
    apply False.elim assump_30


variable (p6 p0 p1 p2 p7 p4 p3 p5 : Prop)
theorem file44_26041 : (((((p5 ∨ p7) → (False ∨ p5)) ∧ ((True ∧ p7) → False)) → (((p7 ∨ False) ∨ (p5 → False)) → ((p7 ∧ p3) → (p5 → p2)))) ∨ ((((False → p1) → False) → ((p5 → False) → False)) ∨ (((p5 → False) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p0) → (p5 ∨ p5))))) := by
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    cases assump_10
    case inl assump_21 =>
      cases assump_21
      case inl assump_23 =>
        cases assump_9
        case intro assump_27 assump_28 =>
          have assump_51 : (True ∧ p7) := by
            apply And.intro
            apply True.intro
            exact assump_23
          let assump_33 := assump_28 assump_51
          apply False.elim assump_33
      case inr assump_24 =>
        apply False.elim assump_24
    case inr assump_22 =>
      cases assump_9
      case intro assump_41 assump_42 =>
        have assump_52 : (True ∧ p7) := by
          apply And.intro
          apply True.intro
          exact assump_15
        let assump_47 := assump_42 assump_52
        apply False.elim assump_47


variable (p5 p3 p4 p7 p0 p6 : Prop)
theorem file44_27202 : (((((True ∨ p6) ∨ (True ∨ p7)) ∧ ((p3 ∨ False) ∧ (p3 ∨ True))) ∨ (((p5 ∨ p4) → (p3 → False)) ∧ ((False ∧ p0) ∨ (p5 ∨ p0)))) → ((((p5 → False) → (p4 ∨ True)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_8
          case intro assump_15 assump_16 =>
            cases assump_15
            case inl assump_17 =>
              cases assump_16
              case inl assump_21 =>
                have assump_186 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_28
                  apply Or.inr
                  apply True.intro
                let assump_27 := assump_2 assump_186
                apply False.elim assump_27
              case inr assump_22 =>
                have assump_187 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_38
                  apply Or.inr
                  apply True.intro
                let assump_37 := assump_2 assump_187
                apply False.elim assump_37
            case inr assump_18 =>
              apply False.elim assump_18
        case inr assump_12 =>
          cases assump_8
          case intro assump_48 assump_49 =>
            cases assump_48
            case inl assump_50 =>
              cases assump_49
              case inl assump_54 =>
                have assump_188 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_62
                  apply Or.inr
                  apply True.intro
                let assump_61 := assump_2 assump_188
                apply False.elim assump_61
              case inr assump_55 =>
                have assump_189 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_73
                  apply Or.inr
                  apply True.intro
                let assump_72 := assump_2 assump_189
                apply False.elim assump_72
            case inr assump_51 =>
              apply False.elim assump_51
      case inr assump_10 =>
        cases assump_10
        case inl assump_81 =>
          cases assump_8
          case intro assump_85 assump_86 =>
            cases assump_85
            case inl assump_87 =>
              cases assump_86
              case inl assump_91 =>
                have assump_190 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_98
                  apply Or.inr
                  apply True.intro
                let assump_97 := assump_2 assump_190
                apply False.elim assump_97
              case inr assump_92 =>
                have assump_191 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_108
                  apply Or.inr
                  apply True.intro
                let assump_107 := assump_2 assump_191
                apply False.elim assump_107
            case inr assump_88 =>
              apply False.elim assump_88
        case inr assump_82 =>
          cases assump_8
          case intro assump_118 assump_119 =>
            cases assump_118
            case inl assump_120 =>
              cases assump_119
              case inl assump_124 =>
                have assump_192 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_132
                  apply Or.inr
                  apply True.intro
                let assump_131 := assump_2 assump_192
                apply False.elim assump_131
              case inr assump_125 =>
                have assump_193 : ((p5 → False) → (p4 ∨ True)) := by
                  intro assump_143
                  apply Or.inr
                  apply True.intro
                let assump_142 := assump_2 assump_193
                apply False.elim assump_142
            case inr assump_121 =>
              apply False.elim assump_121
  case inr assump_6 =>
    cases assump_6
    case intro assump_151 assump_152 =>
      cases assump_152
      case inl assump_155 =>
        cases assump_155
        case intro assump_157 assump_158 =>
          apply False.elim assump_157
      case inr assump_156 =>
        cases assump_156
        case inl assump_161 =>
          have assump_194 : ((p5 → False) → (p4 ∨ True)) := by
            intro assump_169
            apply Or.inr
            apply True.intro
          let assump_168 := assump_2 assump_194
          apply False.elim assump_168
        case inr assump_162 =>
          have assump_195 : ((p5 → False) → (p4 ∨ True)) := by
            intro assump_180
            apply Or.inr
            apply True.intro
          let assump_179 := assump_2 assump_195
          apply False.elim assump_179


variable (p2 p7 : Prop)
theorem file44_31995 : ((((((p7 ∨ p2) → (p7 → p7)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p7 ∨ p2) → (p7 → p7)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p7 ∨ p2) → (p7 → p7)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case inl assump_13 =>
        exact assump_13
      case inr assump_14 =>
        exact assump_10
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p5 p0 p6 p4 p1 p3 : Prop)
theorem file44_32586 : ((((((p2 ∨ p4) ∧ (p1 → False)) ∨ ((p5 → p4) ∨ (p0 ∨ p2))) → (((False ∨ p5) → (p6 ∨ p1)) → ((p6 ∨ p0) → False))) ∧ ((((p1 ∧ p2) → (False → False)) → False) ∧ (((p6 ∨ p4) ∨ (p4 ∨ p3)) → ((p2 → p6) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_21 : ((p1 ∧ p2) → (False → False)) := by
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13


variable (p6 p2 p1 p3 p4 p7 p0 : Prop)
theorem file44_33220 : (((((p4 ∧ False) ∧ (p3 ∨ p0)) ∧ ((p4 ∨ p3) ∧ (p1 → False))) → (((True ∨ p6) ∨ (p4 → False)) → ((p6 ∧ p6) ∧ (p0 → False)))) ∨ ((((p4 ∨ p7) ∨ (p7 ∧ p1)) → False) ∧ (((p2 → False) → (p3 → False)) ∧ ((p7 ∨ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case intro assump_13 assump_14 =>
            apply False.elim assump_14
    case inr assump_6 =>
      cases assump_1
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            apply False.elim assump_26
  case inr assump_4 =>
    cases assump_1
    case intro assump_33 assump_34 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          apply False.elim assump_38
  cases assump_2
  case inl assump_43 =>
    cases assump_43
    case inl assump_45 =>
      cases assump_1
      case intro assump_49 assump_50 =>
        cases assump_49
        case intro assump_51 assump_52 =>
          cases assump_51
          case intro assump_53 assump_54 =>
            apply False.elim assump_54
    case inr assump_46 =>
      cases assump_1
      case intro assump_61 assump_62 =>
        cases assump_61
        case intro assump_63 assump_64 =>
          cases assump_63
          case intro assump_65 assump_66 =>
            apply False.elim assump_66
  case inr assump_44 =>
    cases assump_1
    case intro assump_73 assump_74 =>
      cases assump_73
      case intro assump_75 assump_76 =>
        cases assump_75
        case intro assump_77 assump_78 =>
          apply False.elim assump_78
  intro assump_83
  cases assump_2
  case inl assump_86 =>
    cases assump_86
    case inl assump_88 =>
      cases assump_1
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_94
          case intro assump_96 assump_97 =>
            apply False.elim assump_97
    case inr assump_89 =>
      cases assump_1
      case intro assump_104 assump_105 =>
        cases assump_104
        case intro assump_106 assump_107 =>
          cases assump_106
          case intro assump_108 assump_109 =>
            apply False.elim assump_109
  case inr assump_87 =>
    cases assump_1
    case intro assump_116 assump_117 =>
      cases assump_116
      case intro assump_118 assump_119 =>
        cases assump_118
        case intro assump_120 assump_121 =>
          apply False.elim assump_121


variable (p3 p1 p6 p5 p7 p2 : Prop)
theorem file44_36111 : (((((False ∧ p5) ∧ (True ∨ True)) ∧ ((p5 → p2) ∨ (p6 ∧ p7))) ∧ (((True ∧ False) ∨ (p3 ∧ p1)) ∧ ((p2 → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8


variable (p6 p5 p4 p7 p1 p3 p0 p2 : Prop)
theorem file44_36593 : (((((p1 ∨ p0) → False) → ((True → False) → (p5 → False))) ∨ (((p7 ∨ p6) → (p0 → p5)) → False)) ∨ ((((False ∧ p3) → (False ∧ False)) ∨ ((p5 → False) → (p5 → p7))) → (((p2 ∧ p5) ∨ (p3 → p6)) ∨ ((False → p3) → (p4 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_15 : True := by
    apply True.intro
  let assump_11 := assump_2 assump_15
  apply False.elim assump_11


variable (p5 p0 p6 p4 p3 p7 p1 p2 : Prop)
theorem file44_37088 : (((((p1 ∧ p4) ∨ (p0 ∧ p1)) → ((p0 ∨ p7) → False)) → (((p2 → p0) → (p4 → True)) ∨ ((p1 ∨ False) → False))) ∧ ((((p5 ∧ p6) ∧ (p6 → False)) ∧ ((p7 ∧ p3) ∧ (p2 → p1))) → (((p7 → False) → False) ∧ ((False ∧ p5) → False)))) := by
  apply And.intro
  intro assump_20
  apply Or.inl
  intro assump_23
  intro assump_24
  apply True.intro
  intro assump_25
  apply And.intro
  intro assump_26
  cases assump_25
  case intro assump_29 assump_30 =>
    cases assump_29
    case intro assump_31 assump_32 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        cases assump_30
        case intro assump_41 assump_42 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            have assump_63 : p6 := by
              exact assump_34
            let assump_54 := assump_32 assump_63
            apply False.elim assump_54
  intro assump_58
  cases assump_58
  case intro assump_59 assump_60 =>
    apply False.elim assump_59


variable (p1 p2 p7 p5 : Prop)
theorem file44_38095 : (((((p1 → False) → False) → ((p5 ∧ False) → (True ∨ p7))) → (((p5 ∧ False) → (p2 ∨ p7)) → False)) → False) := by
  intro assump_1
  have assump_24 : (((p1 → False) → False) → ((p5 ∧ False) → (True ∨ p7))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_24
  have assump_25 : ((p5 ∧ False) → (p2 ∨ p7)) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_16
  let assump_13 := assump_4 assump_25
  apply False.elim assump_13


variable (p6 p5 p4 p7 p0 p2 p3 : Prop)
theorem file44_38761 : (((((p7 → False) → False) → ((p5 ∨ p0) ∨ (p7 ∨ False))) → False) → ((((p0 → True) → (p0 ∨ p7)) ∨ ((True ∨ p4) → (p6 ∧ p2))) → (((p2 ∨ p3) ∧ (p7 ∧ False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_5
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    case inr assump_7 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        apply False.elim assump_19


variable (p4 p0 p6 p5 p3 p1 : Prop)
theorem file44_39355 : (((((p4 ∧ p5) → False) ∧ ((True → p6) ∧ (True ∧ p0))) ∧ (((p1 → False) ∧ (p3 → False)) → False)) → ((((p1 ∧ p3) ∨ (p1 → False)) ∨ ((p1 ∨ p6) → (p1 ∧ p1))) → (((p5 ∧ True) → (p0 → p3)) → ((p5 ∧ False) → (p6 → p0))))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_8
  case intro assump_12 assump_13 =>
    apply False.elim assump_13


variable (p6 p4 p2 p5 p3 p1 p0 : Prop)
theorem file44_39809 : (((((p4 → False) ∨ (p4 → p2)) ∨ ((p1 ∧ p3) → False)) ∧ (((False ∧ p0) ∧ (p1 → p0)) → False)) → ((((p6 → p6) ∨ (p6 → p0)) → ((p0 ∧ p0) ∧ (False ∧ p0))) → (((p4 → p6) ∨ (p3 → p2)) ∧ ((p4 ∧ True) ∧ (False ∨ p5))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_15
        have assump_193 : p4 := by
          exact assump_15
        let assump_20 := assump_9 assump_193
        apply False.elim assump_20
      case inr assump_10 =>
        apply Or.inl
        intro assump_28
        have assump_194 : ((p6 → p6) ∨ (p6 → p0)) := by
          apply Or.inl
          intro assump_36
          exact assump_36
        let assump_35 := assump_2 assump_194
        let assump_39 := And.right assump_35
        let assump_43 := And.left assump_39
        apply False.elim assump_43
    case inr assump_8 =>
      apply Or.inl
      intro assump_51
      have assump_195 : ((p6 → p6) ∨ (p6 → p0)) := by
        apply Or.inl
        intro assump_58
        exact assump_58
      let assump_57 := assump_2 assump_195
      let assump_61 := And.right assump_57
      let assump_65 := And.left assump_61
      apply False.elim assump_65
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_71 assump_72 =>
    cases assump_71
    case inl assump_73 =>
      cases assump_73
      case inl assump_75 =>
        have assump_196 : ((p6 → p6) ∨ (p6 → p0)) := by
          apply Or.inl
          intro assump_84
          exact assump_84
        let assump_83 := assump_2 assump_196
        let assump_87 := And.right assump_83
        let assump_91 := And.left assump_87
        apply False.elim assump_91
      case inr assump_76 =>
        have assump_197 : ((p6 → p6) ∨ (p6 → p0)) := by
          apply Or.inl
          intro assump_102
          exact assump_102
        let assump_101 := assump_2 assump_197
        let assump_105 := And.right assump_101
        let assump_109 := And.left assump_105
        apply False.elim assump_109
    case inr assump_74 =>
      have assump_198 : ((p6 → p6) ∨ (p6 → p0)) := by
        apply Or.inl
        intro assump_120
        exact assump_120
      let assump_119 := assump_2 assump_198
      let assump_123 := And.right assump_119
      let assump_127 := And.left assump_123
      apply False.elim assump_127
  apply True.intro
  cases assump_1
  case intro assump_133 assump_134 =>
    cases assump_133
    case inl assump_135 =>
      cases assump_135
      case inl assump_137 =>
        have assump_199 : ((p6 → p6) ∨ (p6 → p0)) := by
          apply Or.inl
          intro assump_146
          exact assump_146
        let assump_145 := assump_2 assump_199
        let assump_149 := And.right assump_145
        let assump_153 := And.left assump_149
        apply False.elim assump_153
      case inr assump_138 =>
        have assump_200 : ((p6 → p6) ∨ (p6 → p0)) := by
          apply Or.inl
          intro assump_164
          exact assump_164
        let assump_163 := assump_2 assump_200
        let assump_167 := And.right assump_163
        let assump_171 := And.left assump_167
        apply False.elim assump_171
    case inr assump_136 =>
      have assump_201 : ((p6 → p6) ∨ (p6 → p0)) := by
        apply Or.inl
        intro assump_182
        exact assump_182
      let assump_181 := assump_2 assump_201
      let assump_185 := And.right assump_181
      let assump_189 := And.left assump_185
      apply False.elim assump_189


variable (p6 p7 p1 p3 p2 p4 p5 : Prop)
theorem file44_43471 : ((((((True ∨ p1) → False) → ((p6 → p5) ∧ (p1 ∨ p7))) ∨ (((True → p4) ∧ (p7 ∨ p6)) ∧ ((True → p6) ∧ (p5 ∧ p1)))) → ((((p7 → False) ∧ (p2 → False)) ∧ ((False ∧ p3) ∧ (p2 → p3))) ∧ (((True → p5) ∨ (p4 → p7)) → False))) → False) := by
  intro assump_1
  have assump_31 : ((((True ∨ p1) → False) → ((p6 → p5) ∧ (p1 ∨ p7))) ∨ (((True → p4) ∧ (p7 ∨ p6)) ∧ ((True → p6) ∧ (p5 ∧ p1)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_32 : (True ∨ p1) := by
      apply Or.inl
      apply True.intro
    let assump_11 := assump_5 assump_32
    apply False.elim assump_11
    have assump_33 : (True ∨ p1) := by
      apply Or.inl
      apply True.intro
    let assump_17 := assump_5 assump_33
    apply False.elim assump_17
  let assump_4 := assump_1 assump_31
  let assump_21 := And.left assump_4
  let assump_22 := And.right assump_21
  let assump_26 := And.left assump_22
  let assump_27 := And.left assump_26
  apply False.elim assump_27


variable (p2 p6 p5 p4 p1 p3 p0 : Prop)
theorem file44_44514 : (((((p2 ∧ p1) ∨ (p2 ∧ p4)) → ((p6 → p3) ∨ (p6 → p2))) → (((p2 → p0) ∧ (p4 ∨ p4)) → ((p5 → p6) → (False → False)))) ∨ ((((p6 → False) → (False → False)) → False) ∧ (((p5 → False) ∨ (p1 → p2)) ∧ ((True ∨ p5) ∨ (p2 → p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p7 p6 p3 p4 p5 p2 p0 : Prop)
theorem file44_44916 : (((((p7 ∨ p0) ∧ (False ∨ True)) → ((p7 → False) ∧ (True ∨ p3))) → (((True ∧ p7) → False) ∨ ((p3 ∨ p0) → False))) ∧ ((((False → p6) ∧ (False → False)) → ((p2 ∧ p5) → False)) → (((p2 ∨ p4) ∨ (p6 → p6)) ∨ ((p5 ∧ False) → False)))) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_24 : ((p7 ∨ p0) ∧ (False ∨ True)) := by
      apply And.intro
      apply Or.inl
      exact assump_6
      apply Or.inr
      apply True.intro
    let assump_12 := assump_1 assump_24
    let assump_13 := And.left assump_12
    have assump_25 : p7 := by
      exact assump_6
    let assump_14 := assump_13 assump_25
    apply False.elim assump_14
  intro assump_18
  apply Or.inl
  apply Or.inr
  intro assump_21
  exact assump_21


variable (p4 p6 p0 p5 p1 p7 : Prop)
theorem file44_45775 : (((((p4 → p0) → False) → ((False → False) ∨ (p5 ∨ p7))) ∧ (((p4 → p4) → False) ∧ ((p1 → p5) ∨ (p6 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_32 : (p4 → p4) := by
          intro assump_16
          exact assump_16
        let assump_15 := assump_6 assump_32
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_33 : (p4 → p4) := by
          intro assump_26
          exact assump_26
        let assump_25 := assump_6 assump_33
        apply False.elim assump_25


variable (p2 p0 p3 p4 p7 p6 : Prop)
theorem file44_46504 : (((((p6 → p2) ∨ (p4 → p3)) ∧ ((p0 ∧ p7) ∨ (False → False))) ∧ (((p0 ∧ p4) → (p0 ∧ p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_108 : ((p0 ∧ p4) → (p0 ∧ p0)) := by
              intro assump_21
              apply And.intro
              cases assump_21
              case intro assump_22 assump_23 =>
                exact assump_22
              cases assump_21
              case intro assump_28 assump_29 =>
                exact assump_28
            let assump_20 := assump_3 assump_108
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_109 : ((p0 ∧ p4) → (p0 ∧ p0)) := by
            intro assump_42
            apply And.intro
            cases assump_42
            case intro assump_43 assump_44 =>
              exact assump_43
            cases assump_42
            case intro assump_49 assump_50 =>
              exact assump_49
          let assump_41 := assump_3 assump_109
          apply False.elim assump_41
      case inr assump_7 =>
        cases assump_5
        case inl assump_60 =>
          cases assump_60
          case intro assump_62 assump_63 =>
            have assump_110 : ((p0 ∧ p4) → (p0 ∧ p0)) := by
              intro assump_71
              apply And.intro
              cases assump_71
              case intro assump_72 assump_73 =>
                exact assump_72
              cases assump_71
              case intro assump_78 assump_79 =>
                exact assump_78
            let assump_70 := assump_3 assump_110
            apply False.elim assump_70
        case inr assump_61 =>
          have assump_111 : ((p0 ∧ p4) → (p0 ∧ p0)) := by
            intro assump_92
            apply And.intro
            cases assump_92
            case intro assump_93 assump_94 =>
              exact assump_93
            cases assump_92
            case intro assump_99 assump_100 =>
              exact assump_99
          let assump_91 := assump_3 assump_111
          apply False.elim assump_91


variable (p0 p3 p5 p1 p7 p2 p4 p6 : Prop)
theorem file44_48855 : (((((p6 ∧ p7) → (p6 → True)) ∨ ((p7 → False) ∨ (p2 → p3))) → False) → ((((p4 → False) → False) ∧ ((p6 ∨ p5) → (p1 → p5))) → (((p6 ∧ p0) → False) → ((p7 ∨ p4) → False)))) := by
  intro assump_16
  intro assump_17
  intro assump_18
  intro assump_19
  cases assump_19
  case inl assump_20 =>
    cases assump_17
    case intro assump_26 assump_27 =>
      have assump_58 : (((p6 ∧ p7) → (p6 → True)) ∨ ((p7 → False) ∨ (p2 → p3))) := by
        apply Or.inl
        intro assump_35
        intro assump_36
        apply True.intro
      let assump_34 := assump_16 assump_58
      apply False.elim assump_34
  case inr assump_21 =>
    cases assump_17
    case intro assump_44 assump_45 =>
      have assump_59 : (((p6 ∧ p7) → (p6 → True)) ∨ ((p7 → False) ∨ (p2 → p3))) := by
        apply Or.inl
        intro assump_53
        intro assump_54
        apply True.intro
      let assump_52 := assump_16 assump_59
      apply False.elim assump_52


variable (p3 : Prop)
theorem file44_49842 : (((((True ∨ p3) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p3) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p3) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p1 p5 p3 : Prop)
theorem file44_50262 : ((((((p0 → p1) → (p3 ∨ False)) → ((p3 ∧ p5) ∧ (False ∨ True))) → False) ∧ ((((False → p0) → False) → ((p1 ∧ p3) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_29 : (((False → p0) → False) → ((p1 ∧ p3) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_30 : (False → p0) := by
          intro assump_20
          apply False.elim assump_20
        let assump_19 := assump_9 assump_30
        apply False.elim assump_19
    let assump_8 := assump_3 assump_29
    apply False.elim assump_8


variable (p5 p7 p6 p1 p2 : Prop)
theorem file44_50968 : ((((((False ∧ p1) → (p5 ∧ p7)) ∧ ((p6 → False) ∧ (p2 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False ∧ p1) → (p5 ∧ p7)) ∧ ((p6 → False) ∧ (p2 ∧ False))) → False) := by
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


variable (p4 p7 p3 p0 p5 p1 p6 p2 : Prop)
theorem file44_51547 : (((((False ∧ p3) → False) ∨ ((p4 ∨ p1) ∧ (p3 → False))) ∨ (((p7 → p3) → False) → ((p2 → False) → (p4 ∨ p6)))) ∨ ((((p3 ∧ p3) ∨ (p0 → p5)) ∧ ((p3 → p5) ∨ (p6 ∨ p5))) → (((p7 ∧ p2) ∧ (p3 → p6)) → ((p2 ∧ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p2 p5 : Prop)
theorem file44_51963 : ((((((p2 ∧ p2) ∧ (p5 ∨ p2)) → ((p5 → False) → False)) → False) ∧ ((((True ∨ p2) → False) → False) → False)) → False) := by
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


variable (p3 : Prop)
theorem file44_52510 : (((((p3 → False) → False) → False) ∧ (((True → True) → (True ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((True → True) → (True ∨ True)) := by
      intro assump_9
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p5 p7 p2 p6 : Prop)
theorem file44_52921 : ((((((False → False) → False) → False) ∨ (((p6 ∨ p7) → False) → ((p3 → p2) ∨ (p5 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p6 ∨ p7) → False) → ((p3 → p2) ∨ (p5 ∧ p2)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p7 p1 p0 p2 p6 p5 p4 : Prop)
theorem file44_53497 : (((((True → p3) ∧ (p3 → False)) ∧ ((p7 → p6) ∧ (p7 ∧ False))) → False) ∨ ((((p5 → p0) ∨ (p2 ∨ p1)) ∧ ((p0 ∨ p4) ∨ (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15


variable (p3 p5 p6 p0 p4 p7 : Prop)
theorem file44_54004 : ((((((False → p5) → False) ∨ ((True ∨ p0) → (p3 → p4))) → (((p0 ∨ True) → (p0 → False)) → ((p0 → False) ∧ (p5 ∨ True)))) → ((((p3 ∨ p6) ∧ (p3 ∧ p7)) → ((p4 ∨ True) ∨ (p6 → p6))) → False)) → False) := by
  intro assump_1
  have assump_65 : ((((False → p5) → False) ∨ ((True ∨ p0) → (p3 → p4))) → (((p0 ∨ True) → (p0 → False)) → ((p0 → False) ∧ (p5 ∨ True)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      have assump_66 : (False → p5) := by
        intro assump_17
        apply False.elim assump_17
      let assump_16 := assump_12 assump_66
      apply False.elim assump_16
    case inr assump_13 =>
      have assump_67 : (p0 ∨ True) := by
        apply Or.inl
        exact assump_7
      let assump_27 := assump_6 assump_67
      have assump_68 : p0 := by
        exact assump_7
      let assump_28 := assump_27 assump_68
      apply False.elim assump_28
    cases assump_5
    case inl assump_34 =>
      apply Or.inr
      apply True.intro
    case inr assump_35 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_65
  have assump_69 : (((p3 ∨ p6) ∧ (p3 ∧ p7)) → ((p4 ∨ True) ∨ (p6 → p6))) := by
    intro assump_41
    cases assump_41
    case intro assump_42 assump_43 =>
      cases assump_42
      case inl assump_44 =>
        cases assump_43
        case intro assump_48 assump_49 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_45 =>
        cases assump_43
        case intro assump_56 assump_57 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
  let assump_40 := assump_4 assump_69
  apply False.elim assump_40


variable (p1 p2 p6 p3 p0 : Prop)
theorem file44_55780 : (((((p6 → False) ∧ (True → False)) → False) → False) → ((((p0 → False) ∧ (p0 → False)) → ((False → p2) → False)) → (((p1 ∨ p3) → False) ∨ ((p0 ∧ p3) → (p2 ∧ p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    have assump_46 : (((p6 → False) ∧ (True → False)) → False) := by
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        have assump_47 : True := by
          apply True.intro
        let assump_21 := assump_16 assump_47
        apply False.elim assump_21
    let assump_13 := assump_1 assump_46
    apply False.elim assump_13
  case inr assump_9 =>
    have assump_48 : (((p6 → False) ∧ (True → False)) → False) := by
      intro assump_32
      cases assump_32
      case intro assump_33 assump_34 =>
        have assump_49 : True := by
          apply True.intro
        let assump_39 := assump_34 assump_49
        apply False.elim assump_39
    let assump_31 := assump_1 assump_48
    apply False.elim assump_31


variable (p0 p6 p1 p2 p3 : Prop)
theorem file44_56871 : (((((p0 → False) ∨ (p6 → p3)) ∨ ((True → False) → False)) ∧ (((p1 ∧ False) → (p1 ∧ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_71 : ((p1 ∧ False) → (p1 ∧ p2)) := by
          intro assump_13
          apply And.intro
          cases assump_13
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
          cases assump_13
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
        let assump_12 := assump_3 assump_71
        apply False.elim assump_12
      case inr assump_7 =>
        have assump_72 : ((p1 ∧ False) → (p1 ∧ p2)) := by
          intro assump_34
          apply And.intro
          cases assump_34
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
          cases assump_34
          case intro assump_41 assump_42 =>
            apply False.elim assump_42
        let assump_33 := assump_3 assump_72
        apply False.elim assump_33
    case inr assump_5 =>
      have assump_73 : ((p1 ∧ False) → (p1 ∧ p2)) := by
        intro assump_55
        apply And.intro
        cases assump_55
        case intro assump_56 assump_57 =>
          apply False.elim assump_57
        cases assump_55
        case intro assump_62 assump_63 =>
          apply False.elim assump_63
      let assump_54 := assump_3 assump_73
      apply False.elim assump_54


variable (p3 p1 p5 p4 p7 : Prop)
theorem file44_58452 : (((((True ∨ p7) → (p3 → True)) ∧ ((True ∧ p4) ∨ (False → p1))) ∧ (((p1 ∨ p3) → (p7 → p7)) ∨ ((p4 → p5) → False))) ∨ ((((False ∧ p1) → False) → False) → (((p3 → False) ∨ (p5 → False)) ∨ ((p1 → True) → False)))) := by
  apply Or.inl
  apply And.intro
  apply And.intro
  intro assump_1
  intro assump_2
  apply True.intro
  apply Or.inr
  intro assump_3
  apply False.elim assump_3
  apply Or.inl
  intro assump_6
  intro assump_7
  cases assump_6
  case inl assump_10 =>
    exact assump_7
  case inr assump_11 =>
    exact assump_7


variable (p5 p4 p0 p2 p6 p3 p7 : Prop)
theorem file44_59047 : (((((p4 ∨ p7) ∨ (p0 ∧ p5)) → ((p6 ∨ p6) ∧ (p6 → False))) ∧ (((True ∨ False) → False) ∧ ((p2 ∧ p0) → (p3 ∧ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : (True ∨ False) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_6 assump_17
      apply False.elim assump_13


variable (p3 p7 p4 p1 p6 p2 p0 : Prop)
theorem file44_59526 : (((((False ∨ p0) ∧ (p4 ∨ p0)) ∧ ((p6 ∨ p7) ∨ (p1 → False))) ∧ (((p2 → p3) → (p0 ∨ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          apply False.elim assump_8
        case inr assump_9 =>
          cases assump_7
          case inl assump_14 =>
            cases assump_5
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                have assump_94 : ((p2 → p3) → (p0 ∨ p4)) := by
                  intro assump_27
                  apply Or.inl
                  exact assump_9
                let assump_26 := assump_3 assump_94
                apply False.elim assump_26
              case inr assump_21 =>
                have assump_95 : ((p2 → p3) → (p0 ∨ p4)) := by
                  intro assump_38
                  apply Or.inl
                  exact assump_9
                let assump_37 := assump_3 assump_95
                apply False.elim assump_37
            case inr assump_19 =>
              have assump_96 : ((p2 → p3) → (p0 ∨ p4)) := by
                intro assump_49
                apply Or.inl
                exact assump_9
              let assump_48 := assump_3 assump_96
              apply False.elim assump_48
          case inr assump_15 =>
            cases assump_5
            case inl assump_57 =>
              cases assump_57
              case inl assump_59 =>
                have assump_97 : ((p2 → p3) → (p0 ∨ p4)) := by
                  intro assump_66
                  apply Or.inl
                  exact assump_15
                let assump_65 := assump_3 assump_97
                apply False.elim assump_65
              case inr assump_60 =>
                have assump_98 : ((p2 → p3) → (p0 ∨ p4)) := by
                  intro assump_77
                  apply Or.inl
                  exact assump_15
                let assump_76 := assump_3 assump_98
                apply False.elim assump_76
            case inr assump_58 =>
              have assump_99 : ((p2 → p3) → (p0 ∨ p4)) := by
                intro assump_88
                apply Or.inl
                exact assump_15
              let assump_87 := assump_3 assump_99
              apply False.elim assump_87


variable (p7 p2 p6 p1 p3 p4 p0 : Prop)
theorem file44_61998 : (((((p6 → True) ∨ (p1 → False)) ∨ ((p4 ∨ p3) → (p1 ∨ p0))) → False) → ((((p6 ∧ True) ∨ (p7 ∨ True)) → ((p4 ∨ p4) → (p6 ∨ False))) ∨ (((p2 ∧ p7) ∧ (p1 → p0)) → False))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    cases assump_8
    case inl assump_14 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply Or.inl
        exact assump_16
    case inr assump_15 =>
      cases assump_15
      case inl assump_22 =>
        have assump_70 : (((p6 → True) ∨ (p1 → False)) ∨ ((p4 ∨ p3) → (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          intro assump_29
          apply True.intro
        let assump_28 := assump_5 assump_70
        apply False.elim assump_28
      case inr assump_23 =>
        have assump_71 : (((p6 → True) ∨ (p1 → False)) ∨ ((p4 ∨ p3) → (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          intro assump_37
          apply True.intro
        let assump_36 := assump_5 assump_71
        apply False.elim assump_36
  case inr assump_11 =>
    cases assump_8
    case inl assump_43 =>
      cases assump_43
      case intro assump_45 assump_46 =>
        apply Or.inl
        exact assump_45
    case inr assump_44 =>
      cases assump_44
      case inl assump_51 =>
        have assump_72 : (((p6 → True) ∨ (p1 → False)) ∨ ((p4 ∨ p3) → (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          intro assump_58
          apply True.intro
        let assump_57 := assump_5 assump_72
        apply False.elim assump_57
      case inr assump_52 =>
        have assump_73 : (((p6 → True) ∨ (p1 → False)) ∨ ((p4 ∨ p3) → (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          intro assump_66
          apply True.intro
        let assump_65 := assump_5 assump_73
        apply False.elim assump_65


variable (p3 p2 p4 p7 p1 : Prop)
theorem file44_63936 : ((((((p3 ∧ p2) ∧ (p3 ∨ False)) → False) → (((False ∨ True) ∧ (p7 ∧ p4)) → ((True → False) → (p1 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_54 : ((((p3 ∧ p2) ∧ (p3 ∨ False)) → False) → (((False ∨ True) ∧ (p7 ∧ p4)) → ((True → False) → (p1 ∧ p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        apply False.elim assump_12
      case inr assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          have assump_55 : True := by
            apply True.intro
          let assump_29 := assump_7 assump_55
          apply False.elim assump_29
    cases assump_6
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        apply False.elim assump_37
      case inr assump_38 =>
        cases assump_36
        case intro assump_43 assump_44 =>
          exact assump_43
  let assump_4 := assump_1 assump_54
  apply False.elim assump_4


variable (p4 p2 p1 p0 p6 p5 p3 p7 : Prop)
theorem file44_65066 : ((((((False → p4) → (p2 ∧ p6)) ∧ ((p4 ∧ p0) → False)) ∧ (((p4 ∨ p1) → (p4 ∧ p4)) → ((p7 ∨ p7) ∧ (p1 → False)))) ∧ ((((p3 ∧ p5) ∨ (False → p5)) ∨ ((p5 ∧ p2) ∧ (p5 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_23 : (((p3 ∧ p5) ∨ (False → p5)) ∨ ((p5 ∧ p2) ∧ (p5 ∨ p6))) := by
          apply Or.inl
          apply Or.inr
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p4 p0 p1 : Prop)
theorem file44_65768 : (((((True → False) → False) ∨ ((False → p0) → (p4 ∨ p1))) → False) → False) := by
  intro assump_11
  have assump_25 : (((True → False) → False) ∨ ((False → p0) → (p4 ∨ p1))) := by
    apply Or.inl
    intro assump_15
    have assump_26 : True := by
      apply True.intro
    let assump_18 := assump_15 assump_26
    apply False.elim assump_18
  let assump_14 := assump_11 assump_25
  apply False.elim assump_14


variable (p4 p3 p7 p6 : Prop)
theorem file44_66235 : (((((p4 ∨ p7) → False) ∧ ((False → False) → False)) → False) ∨ ((((False ∨ p6) ∨ (p3 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p0 p2 p5 p3 p7 p6 p4 : Prop)
theorem file44_66666 : (((((True ∨ p0) ∧ (False → False)) ∨ ((False ∧ p5) → (True ∨ p6))) ∨ (((p0 → False) → False) ∨ ((p6 ∧ p3) → False))) ∨ ((((p7 → False) → (p5 → False)) → ((False → p2) ∧ (p4 → False))) ∧ (((False → p2) ∧ (False → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply True.intro
  intro assump_1
  apply False.elim assump_1


variable (p0 p4 p3 p7 p5 p1 : Prop)
theorem file44_67105 : (((((True ∧ True) ∧ (p1 ∧ True)) → ((p0 ∨ True) → (p4 ∨ p7))) ∨ (((p3 ∧ p5) → (p5 ∨ p5)) ∧ ((True → False) → False))) → ((((p7 → False) ∧ (p7 ∨ False)) → False) ∨ (((p1 → p3) → (p1 → p3)) ∧ ((p4 → False) → (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        have assump_44 : p7 := by
          exact assump_11
        let assump_16 := assump_7 assump_44
        apply False.elim assump_16
      case inr assump_12 =>
        apply False.elim assump_12
  case inr assump_3 =>
    cases assump_3
    case intro assump_22 assump_23 =>
      apply Or.inl
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        cases assump_30
        case inl assump_33 =>
          have assump_45 : p7 := by
            exact assump_33
          let assump_38 := assump_29 assump_45
          apply False.elim assump_38
        case inr assump_34 =>
          apply False.elim assump_34


variable (p5 p3 p4 p0 p2 p6 p1 : Prop)
theorem file44_68248 : (((((p2 ∧ p6) → False) → False) → (((p1 → False) ∧ (False ∧ p4)) ∨ ((p1 ∨ p5) → (False → False)))) → ((((p3 → False) ∨ (p0 ∨ False)) ∨ ((p1 → False) ∨ (p3 ∧ True))) → (((p1 → p1) → False) → ((p0 → p0) ∨ (True ∧ p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      apply Or.inl
      intro assump_14
      exact assump_14
    case inr assump_9 =>
      cases assump_9
      case inl assump_17 =>
        apply Or.inl
        intro assump_23
        exact assump_23
      case inr assump_18 =>
        apply False.elim assump_18
  case inr assump_7 =>
    cases assump_7
    case inl assump_28 =>
      apply Or.inl
      intro assump_34
      exact assump_34
    case inr assump_29 =>
      cases assump_29
      case intro assump_37 assump_38 =>
        apply Or.inl
        intro assump_45
        exact assump_45


variable (p0 p5 p2 p1 p6 p4 p3 : Prop)
theorem file44_69228 : (((((p5 ∧ p4) ∧ (p1 → False)) → False) → False) → ((((p1 ∨ True) ∨ (p1 ∧ p3)) ∨ ((p0 ∨ p3) ∧ (p3 ∨ p3))) ∨ (((p2 ∨ p2) → (p3 ∧ p6)) → ((p2 ∨ True) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p6 p4 p1 p3 : Prop)
theorem file44_69543 : ((((((p3 ∨ True) → False) → False) ∧ (((p1 ∧ p6) → (False → p4)) ∨ ((p6 → p6) ∨ (p6 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p3 ∨ True) → False) → False) ∧ (((p1 ∧ p6) → (False → p4)) ∨ ((p6 → p6) ∨ (p6 ∨ False)))) := by
    apply And.intro
    intro assump_5
    have assump_20 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
    apply Or.inl
    intro assump_12
    intro assump_13
    apply False.elim assump_13
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p0 p1 p5 p4 p6 p2 : Prop)
theorem file44_70201 : (((((p2 ∧ p4) → False) ∨ ((p1 ∨ p6) → (p1 → p5))) ∧ (((p0 → True) ∨ (p1 ∧ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_24 : ((p0 → True) ∨ (p1 ∧ p2)) := by
        apply Or.inl
        intro assump_11
        apply True.intro
      let assump_10 := assump_3 assump_24
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_25 : ((p0 → True) ∨ (p1 ∧ p2)) := by
        apply Or.inl
        intro assump_20
        apply True.intro
      let assump_19 := assump_3 assump_25
      apply False.elim assump_19


variable (p6 p3 p4 p1 p2 p0 p5 : Prop)
theorem file44_70905 : (((((True ∧ p3) ∨ (False → p2)) → ((p4 ∧ p2) ∨ (p5 → True))) → False) → ((((p3 → False) → False) ∧ ((p4 ∨ p6) ∨ (p4 → p6))) ∧ (((True ∧ p0) → (p1 → p5)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_69 : (((True ∧ p3) ∨ (False → p2)) → ((p4 ∧ p2) ∨ (p5 → True))) := by
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inr
        intro assump_17
        apply True.intro
    case inr assump_10 =>
      apply Or.inr
      intro assump_20
      apply True.intro
  let assump_7 := assump_1 assump_69
  apply False.elim assump_7
  apply Or.inr
  intro assump_26
  have assump_70 : (((True ∧ p3) ∨ (False → p2)) → ((p4 ∧ p2) ∨ (p5 → True))) := by
    intro assump_31
    cases assump_31
    case inl assump_32 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        apply Or.inr
        intro assump_40
        apply True.intro
    case inr assump_33 =>
      apply Or.inr
      intro assump_43
      apply True.intro
  let assump_30 := assump_1 assump_70
  apply False.elim assump_30
  intro assump_47
  have assump_71 : (((True ∧ p3) ∨ (False → p2)) → ((p4 ∧ p2) ∨ (p5 → True))) := by
    intro assump_53
    cases assump_53
    case inl assump_54 =>
      cases assump_54
      case intro assump_56 assump_57 =>
        apply Or.inr
        intro assump_62
        apply True.intro
    case inr assump_55 =>
      apply Or.inr
      intro assump_65
      apply True.intro
  let assump_52 := assump_1 assump_71
  apply False.elim assump_52


variable (p1 p0 p4 p6 p7 p2 p5 : Prop)
theorem file44_72570 : (((((p7 ∨ p1) → False) ∧ ((False → False) ∨ (p7 → False))) ∨ (((p4 → False) ∨ (p0 ∧ p7)) ∧ ((True → p4) → False))) → ((((p6 → p5) ∧ (False ∨ False)) ∧ ((p2 ∧ p0) → (p2 → p1))) → (((p7 → False) → False) ∨ ((p7 → p5) → False)))) := by
  intro assump_21
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_26
      case inl assump_29 =>
        apply False.elim assump_29
      case inr assump_30 =>
        apply False.elim assump_30


variable (p7 p5 p4 p2 p6 p0 : Prop)
theorem file44_73159 : (((((False ∧ p6) ∧ (p5 → False)) ∧ ((p2 → p4) ∧ (True ∧ p5))) → (((p4 ∨ p0) ∨ (p5 → False)) ∨ ((p2 ∧ False) ∧ (p5 → p5)))) ∨ ((((p6 → False) ∨ (p6 → False)) ∨ ((p6 ∧ p5) → False)) → (((False ∨ p7) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p5 p0 p1 p3 p2 : Prop)
theorem file44_73670 : (((((True ∧ p2) ∧ (p1 ∧ p0)) ∧ ((p3 ∨ p2) → False)) ∧ (((p2 → False) → (p5 ∧ p5)) → ((True ∧ False) ∨ (p1 → False)))) → False) := by
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
            have assump_53 : ((p2 → False) → (p5 ∧ p5)) := by
              intro assump_25
              apply And.intro
              have assump_54 : p2 := by
                exact assump_9
              let assump_28 := assump_25 assump_54
              apply False.elim assump_28
              have assump_55 : p2 := by
                exact assump_9
              let assump_34 := assump_25 assump_55
              apply False.elim assump_34
            let assump_24 := assump_3 assump_53
            cases assump_24
            case inl assump_39 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                apply False.elim assump_42
            case inr assump_40 =>
              have assump_56 : p1 := by
                exact assump_14
              let assump_49 := assump_40 assump_56
              apply False.elim assump_49


variable (p7 p2 p5 p6 : Prop)
theorem file44_75048 : (((((True → False) ∨ (p5 → p5)) → False) ∧ (((False → p7) ∨ (p2 → p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → p7) ∨ (p2 → p6)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p0 p5 p2 p6 p1 p4 : Prop)
theorem file44_75470 : (((((True → False) → (True → p1)) → ((p2 ∧ p1) → (p1 ∧ True))) → (((p6 → True) ∨ (p5 → False)) → False)) → ((((p2 ∧ True) ∧ (False ∨ p6)) ∨ ((p0 ∨ p4) ∨ (p2 → p4))) ∨ (((p4 → p5) ∧ (p3 → False)) → False))) := by
  intro assump_9
  apply Or.inl
  apply Or.inr
  apply Or.inr
  intro assump_12
  have assump_32 : (((True → False) → (True → p1)) → ((p2 ∧ p1) → (p1 ∧ True))) := by
    intro assump_17
    intro assump_18
    apply And.intro
    cases assump_18
    case intro assump_19 assump_20 =>
      exact assump_20
    apply True.intro
  let assump_16 := assump_9 assump_32
  have assump_33 : ((p6 → True) ∨ (p5 → False)) := by
    apply Or.inl
    intro assump_28
    apply True.intro
  let assump_27 := assump_16 assump_33
  apply False.elim assump_27


variable (p7 p4 : Prop)
theorem file44_76275 : (((((p7 → p7) → (False → False)) ∨ ((p4 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : (((p7 → p7) → (False → False)) ∨ ((p4 → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p7 p6 p4 : Prop)
theorem file44_76661 : ((((((p4 ∨ True) ∧ (False → False)) → False) → (((p5 ∧ p5) ∨ (p7 → p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p4 ∨ True) ∧ (False → False)) → False) → (((p5 ∧ p5) ∨ (p7 → p6)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_39 : ((p4 ∨ True) ∧ (False → False)) := by
          apply And.intro
          apply Or.inr
          apply True.intro
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_5 assump_39
        apply False.elim assump_17
    case inr assump_8 =>
      have assump_40 : ((p4 ∨ True) ∧ (False → False)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        intro assump_29
        apply False.elim assump_29
      let assump_28 := assump_5 assump_40
      apply False.elim assump_28
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p4 p1 p6 p0 p2 p7 p5 : Prop)
theorem file44_77730 : (((((p7 ∧ p2) ∨ (True ∨ True)) → ((p1 → False) ∧ (p1 ∧ p0))) ∧ (((p5 ∨ p5) ∧ (p7 → False)) ∧ ((True ∨ p6) ∧ (p6 ∨ p1)))) → ((((False ∧ p2) → False) → False) → (((True ∨ True) ∧ (False ∧ p4)) ∧ ((True → p1) → (False → p2))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_10
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_20
              case inl assump_25 =>
                apply Or.inl
                apply True.intro
              case inr assump_26 =>
                apply Or.inl
                apply True.intro
            case inr assump_22 =>
              cases assump_20
              case inl assump_33 =>
                apply Or.inl
                apply True.intro
              case inr assump_34 =>
                apply Or.inl
                apply True.intro
        case inr assump_14 =>
          cases assump_10
          case intro assump_43 assump_44 =>
            cases assump_43
            case inl assump_45 =>
              cases assump_44
              case inl assump_49 =>
                apply Or.inl
                apply True.intro
              case inr assump_50 =>
                apply Or.inl
                apply True.intro
            case inr assump_46 =>
              cases assump_44
              case inl assump_57 =>
                apply Or.inl
                apply True.intro
              case inr assump_58 =>
                apply Or.inl
                apply True.intro
  apply And.intro
  cases assump_1
  case intro assump_65 assump_66 =>
    cases assump_66
    case intro assump_69 assump_70 =>
      cases assump_69
      case intro assump_71 assump_72 =>
        cases assump_71
        case inl assump_73 =>
          cases assump_70
          case intro assump_79 assump_80 =>
            cases assump_79
            case inl assump_81 =>
              cases assump_80
              case inl assump_85 =>
                have assump_411 : ((False ∧ p2) → False) := by
                  intro assump_99
                  cases assump_99
                  case intro assump_100 assump_101 =>
                    apply False.elim assump_100
                let assump_98 := assump_2 assump_411
                apply False.elim assump_98
              case inr assump_86 =>
                have assump_412 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_112 := assump_65 assump_412
                let assump_113 := And.left assump_112
                have assump_413 : p1 := by
                  exact assump_86
                let assump_114 := assump_113 assump_413
                apply False.elim assump_114
            case inr assump_82 =>
              cases assump_80
              case inl assump_120 =>
                have assump_414 : ((False ∧ p2) → False) := by
                  intro assump_135
                  cases assump_135
                  case intro assump_136 assump_137 =>
                    apply False.elim assump_136
                let assump_134 := assump_2 assump_414
                apply False.elim assump_134
              case inr assump_121 =>
                have assump_415 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_149 := assump_65 assump_415
                let assump_150 := And.left assump_149
                have assump_416 : p1 := by
                  exact assump_121
                let assump_151 := assump_150 assump_416
                apply False.elim assump_151
        case inr assump_74 =>
          cases assump_70
          case intro assump_159 assump_160 =>
            cases assump_159
            case inl assump_161 =>
              cases assump_160
              case inl assump_165 =>
                have assump_417 : ((False ∧ p2) → False) := by
                  intro assump_179
                  cases assump_179
                  case intro assump_180 assump_181 =>
                    apply False.elim assump_180
                let assump_178 := assump_2 assump_417
                apply False.elim assump_178
              case inr assump_166 =>
                have assump_418 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_192 := assump_65 assump_418
                let assump_193 := And.left assump_192
                have assump_419 : p1 := by
                  exact assump_166
                let assump_194 := assump_193 assump_419
                apply False.elim assump_194
            case inr assump_162 =>
              cases assump_160
              case inl assump_200 =>
                have assump_420 : ((False ∧ p2) → False) := by
                  intro assump_215
                  cases assump_215
                  case intro assump_216 assump_217 =>
                    apply False.elim assump_216
                let assump_214 := assump_2 assump_420
                apply False.elim assump_214
              case inr assump_201 =>
                have assump_421 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_229 := assump_65 assump_421
                let assump_230 := And.left assump_229
                have assump_422 : p1 := by
                  exact assump_201
                let assump_231 := assump_230 assump_422
                apply False.elim assump_231
  cases assump_1
  case intro assump_237 assump_238 =>
    cases assump_238
    case intro assump_241 assump_242 =>
      cases assump_241
      case intro assump_243 assump_244 =>
        cases assump_243
        case inl assump_245 =>
          cases assump_242
          case intro assump_251 assump_252 =>
            cases assump_251
            case inl assump_253 =>
              cases assump_252
              case inl assump_257 =>
                have assump_423 : ((False ∧ p2) → False) := by
                  intro assump_271
                  cases assump_271
                  case intro assump_272 assump_273 =>
                    apply False.elim assump_272
                let assump_270 := assump_2 assump_423
                apply False.elim assump_270
              case inr assump_258 =>
                have assump_424 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_284 := assump_237 assump_424
                let assump_285 := And.left assump_284
                have assump_425 : p1 := by
                  exact assump_258
                let assump_286 := assump_285 assump_425
                apply False.elim assump_286
            case inr assump_254 =>
              cases assump_252
              case inl assump_292 =>
                have assump_426 : ((False ∧ p2) → False) := by
                  intro assump_307
                  cases assump_307
                  case intro assump_308 assump_309 =>
                    apply False.elim assump_308
                let assump_306 := assump_2 assump_426
                apply False.elim assump_306
              case inr assump_293 =>
                have assump_427 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_321 := assump_237 assump_427
                let assump_322 := And.left assump_321
                have assump_428 : p1 := by
                  exact assump_293
                let assump_323 := assump_322 assump_428
                apply False.elim assump_323
        case inr assump_246 =>
          cases assump_242
          case intro assump_331 assump_332 =>
            cases assump_331
            case inl assump_333 =>
              cases assump_332
              case inl assump_337 =>
                have assump_429 : ((False ∧ p2) → False) := by
                  intro assump_351
                  cases assump_351
                  case intro assump_352 assump_353 =>
                    apply False.elim assump_352
                let assump_350 := assump_2 assump_429
                apply False.elim assump_350
              case inr assump_338 =>
                have assump_430 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_364 := assump_237 assump_430
                let assump_365 := And.left assump_364
                have assump_431 : p1 := by
                  exact assump_338
                let assump_366 := assump_365 assump_431
                apply False.elim assump_366
            case inr assump_334 =>
              cases assump_332
              case inl assump_372 =>
                have assump_432 : ((False ∧ p2) → False) := by
                  intro assump_387
                  cases assump_387
                  case intro assump_388 assump_389 =>
                    apply False.elim assump_388
                let assump_386 := assump_2 assump_432
                apply False.elim assump_386
              case inr assump_373 =>
                have assump_433 : ((p7 ∧ p2) ∨ (True ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_401 := assump_237 assump_433
                let assump_402 := And.left assump_401
                have assump_434 : p1 := by
                  exact assump_373
                let assump_403 := assump_402 assump_434
                apply False.elim assump_403
  intro assump_407
  intro assump_408
  apply False.elim assump_408


variable (p5 p0 p2 p4 p6 p3 p7 : Prop)
theorem file44_87989 : ((((((p0 → False) ∨ (p3 → False)) ∧ ((p4 ∧ p7) ∧ (p5 ∧ False))) → (((True ∧ p0) ∧ (p2 → p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_56 : ((((p0 → False) ∨ (p3 → False)) ∧ ((p4 ∧ p7) ∧ (p5 ∧ False))) → (((True ∧ p0) ∧ (p2 → p6)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_18
            case intro assump_23 assump_24 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                cases assump_24
                case intro assump_31 assump_32 =>
                  apply False.elim assump_32
          case inr assump_20 =>
            cases assump_18
            case intro assump_39 assump_40 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                cases assump_40
                case intro assump_47 assump_48 =>
                  apply False.elim assump_48
  let assump_4 := assump_1 assump_56
  apply False.elim assump_4


variable (p1 p5 p2 p7 p6 p3 p0 p4 : Prop)
theorem file44_89256 : (((((p4 ∧ p6) ∧ (p7 ∧ p0)) → ((True ∨ p0) ∧ (p3 → True))) → False) → ((((p5 ∨ p1) ∨ (p5 → p2)) → False) ∧ (((p1 ∧ p2) ∧ (p3 ∧ p3)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      have assump_116 : (((p4 ∧ p6) ∧ (p7 ∧ p0)) → ((True ∨ p0) ∧ (p3 → True))) := by
        intro assump_12
        apply And.intro
        cases assump_12
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_14
            case intro assump_21 assump_22 =>
              apply Or.inl
              apply True.intro
        intro assump_27
        apply True.intro
      let assump_11 := assump_1 assump_116
      apply False.elim assump_11
    case inr assump_6 =>
      have assump_117 : (((p4 ∧ p6) ∧ (p7 ∧ p0)) → ((True ∨ p0) ∧ (p3 → True))) := by
        intro assump_36
        apply And.intro
        cases assump_36
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            cases assump_38
            case intro assump_45 assump_46 =>
              apply Or.inl
              apply True.intro
        intro assump_51
        apply True.intro
      let assump_35 := assump_1 assump_117
      apply False.elim assump_35
  case inr assump_4 =>
    have assump_118 : (((p4 ∧ p6) ∧ (p7 ∧ p0)) → ((True ∨ p0) ∧ (p3 → True))) := by
      intro assump_60
      apply And.intro
      cases assump_60
      case intro assump_61 assump_62 =>
        cases assump_61
        case intro assump_63 assump_64 =>
          cases assump_62
          case intro assump_69 assump_70 =>
            apply Or.inl
            apply True.intro
      intro assump_75
      apply True.intro
    let assump_59 := assump_1 assump_118
    apply False.elim assump_59
  intro assump_79
  cases assump_79
  case intro assump_80 assump_81 =>
    cases assump_80
    case intro assump_82 assump_83 =>
      cases assump_81
      case intro assump_88 assump_89 =>
        have assump_119 : (((p4 ∧ p6) ∧ (p7 ∧ p0)) → ((True ∨ p0) ∧ (p3 → True))) := by
          intro assump_97
          apply And.intro
          cases assump_97
          case intro assump_98 assump_99 =>
            cases assump_98
            case intro assump_100 assump_101 =>
              cases assump_99
              case intro assump_106 assump_107 =>
                apply Or.inl
                apply True.intro
          intro assump_112
          apply True.intro
        let assump_96 := assump_1 assump_119
        apply False.elim assump_96


variable (p3 p2 p4 p1 p7 p6 : Prop)
theorem file44_91953 : ((((((p3 → p4) ∧ (p7 ∨ p1)) ∧ ((p4 ∨ True) → False)) → (((False ∨ p6) → False) ∧ ((p7 → p2) → False))) → False) → False) := by
  intro assump_1
  have assump_67 : ((((p3 → p4) ∧ (p7 ∨ p1)) ∧ ((p4 ∨ True) → False)) → (((False ∨ p6) → False) ∧ ((p7 → p2) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply False.elim assump_7
    case inr assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            have assump_68 : (p4 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_25 := assump_14 assump_68
            apply False.elim assump_25
          case inr assump_20 =>
            have assump_69 : (p4 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_33 := assump_14 assump_69
            apply False.elim assump_33
    intro assump_37
    cases assump_5
    case intro assump_40 assump_41 =>
      cases assump_40
      case intro assump_42 assump_43 =>
        cases assump_43
        case inl assump_46 =>
          have assump_70 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_52 := assump_41 assump_70
          apply False.elim assump_52
        case inr assump_47 =>
          have assump_71 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_60 := assump_41 assump_71
          apply False.elim assump_60
  let assump_4 := assump_1 assump_67
  apply False.elim assump_4


variable (p5 p2 p7 p0 p3 p6 p1 p4 : Prop)
theorem file44_93705 : (((((p6 → True) → False) → ((p0 ∧ p3) → False)) ∨ (((p3 ∧ p0) → (p4 → False)) ∨ ((p7 ∨ p2) ∨ (p5 ∧ p1)))) ∨ ((((p1 ∨ p6) ∨ (p7 → p1)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_16 : (p6 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_1 assump_16
    apply False.elim assump_11


variable (p7 p5 p2 p1 p6 p0 p4 : Prop)
theorem file44_94197 : ((((((p5 ∨ p6) ∨ (p6 → False)) ∨ ((p2 → p4) ∧ (p5 → p1))) → (((False ∧ p0) ∧ (p1 → p1)) → ((True ∨ p2) ∨ (p7 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p5 ∨ p6) ∨ (p6 → False)) ∨ ((p2 → p4) ∧ (p5 → p1))) → (((False ∧ p0) ∧ (p1 → p1)) → ((True ∨ p2) ∨ (p7 ∧ p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p0 p7 p1 p4 : Prop)
theorem file44_94806 : (((((p7 → False) ∧ (p3 ∨ p3)) ∧ ((p1 → False) ∧ (True ∧ False))) ∨ (((p1 ∧ p1) → (p0 → p7)) ∧ ((p4 ∨ True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              apply False.elim assump_19
        case inr assump_11 =>
          cases assump_5
          case intro assump_26 assump_27 =>
            cases assump_27
            case intro assump_30 assump_31 =>
              apply False.elim assump_31
  case inr assump_3 =>
    cases assump_3
    case intro assump_36 assump_37 =>
      have assump_46 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_42 := assump_37 assump_46
      apply False.elim assump_42


variable (p2 p0 p4 p3 p5 p1 p6 p7 : Prop)
theorem file44_95870 : (((((p4 ∨ p0) ∧ (p0 ∧ p5)) ∧ ((p5 → False) ∧ (p0 → p7))) → (((p6 → False) → False) ∧ ((p4 → False) ∧ (True ∧ p3)))) ∨ ((((p5 → False) ∨ (p6 ∨ p2)) ∨ ((False → p3) ∧ (False ∨ True))) ∨ (((True → p0) ∨ (p3 ∧ True)) → ((p7 → p0) ∧ (p2 → p1))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_6
          case intro assump_19 assump_20 =>
            have assump_146 : p5 := by
              exact assump_14
            let assump_27 := assump_19 assump_146
            apply False.elim assump_27
      case inr assump_10 =>
        cases assump_8
        case intro assump_33 assump_34 =>
          cases assump_6
          case intro assump_39 assump_40 =>
            have assump_147 : p5 := by
              exact assump_34
            let assump_47 := assump_39 assump_147
            apply False.elim assump_47
  apply And.intro
  intro assump_51
  cases assump_1
  case intro assump_54 assump_55 =>
    cases assump_54
    case intro assump_56 assump_57 =>
      cases assump_56
      case inl assump_58 =>
        cases assump_57
        case intro assump_62 assump_63 =>
          cases assump_55
          case intro assump_68 assump_69 =>
            have assump_148 : p5 := by
              exact assump_63
            let assump_76 := assump_68 assump_148
            apply False.elim assump_76
      case inr assump_59 =>
        cases assump_57
        case intro assump_82 assump_83 =>
          cases assump_55
          case intro assump_88 assump_89 =>
            have assump_149 : p5 := by
              exact assump_83
            let assump_96 := assump_88 assump_149
            apply False.elim assump_96
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_100 assump_101 =>
    cases assump_100
    case intro assump_102 assump_103 =>
      cases assump_102
      case inl assump_104 =>
        cases assump_103
        case intro assump_108 assump_109 =>
          cases assump_101
          case intro assump_114 assump_115 =>
            have assump_150 : p5 := by
              exact assump_109
            let assump_122 := assump_114 assump_150
            apply False.elim assump_122
      case inr assump_105 =>
        cases assump_103
        case intro assump_128 assump_129 =>
          cases assump_101
          case intro assump_134 assump_135 =>
            have assump_151 : p5 := by
              exact assump_129
            let assump_142 := assump_134 assump_151
            apply False.elim assump_142


variable (p1 p4 p6 p2 p5 p3 p0 : Prop)
theorem file44_98669 : (((((p0 ∨ p1) ∧ (p2 → False)) ∧ ((True → False) ∧ (p2 → False))) → False) ∨ ((((p6 ∧ p5) → (p1 → False)) ∧ ((p0 → False) ∨ (False → False))) ∨ (((True ∧ p4) → (True ∨ p3)) ∨ ((False ∧ p4) → False)))) := by
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
          have assump_38 : True := by
            apply True.intro
          let assump_19 := assump_12 assump_38
          apply False.elim assump_19
      case inr assump_7 =>
        cases assump_3
        case intro assump_27 assump_28 =>
          have assump_39 : True := by
            apply True.intro
          let assump_34 := assump_27 assump_39
          apply False.elim assump_34


variable (p2 p5 p3 p7 : Prop)
theorem file44_99574 : (((((False ∧ p3) ∧ (p2 → p2)) → ((p3 ∨ p7) ∧ (p7 → p5))) → False) → False) := by
  intro assump_5
  have assump_28 : (((False ∧ p3) ∧ (p2 → p2)) → ((p3 ∨ p7) ∧ (p7 → p5))) := by
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
    intro assump_16
    cases assump_9
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        apply False.elim assump_21
  let assump_8 := assump_5 assump_28
  apply False.elim assump_8


variable (p6 p2 p1 p7 p3 p0 p5 p4 : Prop)
theorem file44_100250 : (((((p7 → p7) → False) → ((p4 → False) → False)) ∨ (((p6 → p3) ∧ (p2 ∨ p1)) ∧ ((False → p3) ∧ (p7 ∧ True)))) ∧ ((((p5 → False) ∨ (True ∨ p6)) → ((p0 ∧ p6) → (p1 → p1))) ∨ (((p1 → p4) ∧ (p2 ∧ p1)) ∨ ((p6 ∧ p0) ∧ (p2 → False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_35 : (p7 → p7) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_1 assump_35
  apply False.elim assump_7
  apply Or.inl
  intro assump_14
  intro assump_15
  intro assump_16
  cases assump_15
  case intro assump_19 assump_20 =>
    cases assump_14
    case inl assump_25 =>
      exact assump_16
    case inr assump_26 =>
      cases assump_26
      case inl assump_29 =>
        exact assump_16
      case inr assump_30 =>
        exact assump_16


variable (p0 p5 p3 p1 p2 p4 p7 p6 : Prop)
theorem file44_101098 : ((((((p1 → False) → (p7 → False)) ∨ ((p0 ∨ p2) → (p6 → p3))) → False) ∧ ((((p5 → False) ∧ (False ∧ p3)) → ((False ∨ p0) ∨ (p4 → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p5 → False) ∧ (False ∧ p3)) → ((False ∨ p0) ∨ (p4 → p3))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p4 p3 p0 : Prop)
theorem file44_101718 : ((((((p0 ∧ False) → (p3 → False)) → False) → (((p3 → False) → (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p0 ∧ False) → (p3 → False)) → False) → (((p3 → False) → (p4 → False)) → False)) := by
    intro assump_5
    intro assump_6
    have assump_29 : ((p0 ∧ False) → (p3 → False)) := by
      intro assump_12
      intro assump_13
      cases assump_12
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    let assump_11 := assump_5 assump_29
    apply False.elim assump_11
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p0 p6 p3 : Prop)
theorem file44_102377 : (((((p0 → False) → (False → False)) ∧ ((p3 ∨ p3) ∨ (p3 → p6))) → False) → False) := by
  intro assump_1
  have assump_24 : (((p0 → False) → (False → False)) ∧ ((p3 ∨ p3) ∨ (p3 → p6))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    apply Or.inr
    intro assump_9
    have assump_25 : (((p0 → False) → (False → False)) ∧ ((p3 ∨ p3) ∨ (p3 → p6))) := by
      apply And.intro
      intro assump_14
      intro assump_15
      apply False.elim assump_15
      apply Or.inl
      apply Or.inl
      exact assump_9
    let assump_13 := assump_1 assump_25
    apply False.elim assump_13
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p1 p7 p6 p2 p0 p5 p3 : Prop)
theorem file44_103136 : (((((p1 → True) ∧ (p2 ∧ p3)) ∨ ((False ∨ p7) → False)) → (((p0 ∧ p5) ∧ (p5 ∧ p2)) ∧ ((p1 → p3) ∧ (p1 → False)))) → ((((p1 → False) ∨ (True → False)) → ((p6 ∨ False) ∨ (False → False))) ∨ (((True ∧ False) → False) ∧ ((p7 ∧ p2) ∧ (p6 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
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


variable (p1 p0 p6 p2 p4 p5 p7 p3 : Prop)
theorem file44_103696 : (((((p1 → p1) ∨ (p7 ∨ p7)) ∨ ((p3 → False) ∨ (p5 → p5))) ∨ (((p5 ∨ p0) → False) ∨ ((p6 → False) → (p7 ∧ True)))) ∨ ((((False → False) → False) → ((p7 → p2) ∨ (p6 ∨ p0))) → (((p4 → False) ∨ (p4 ∧ p4)) ∧ ((p2 ∨ p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_38
  exact assump_38


variable (p0 p4 p5 p2 p3 p7 p6 : Prop)
theorem file44_104086 : (((((p4 → False) ∧ (p2 ∧ p4)) ∧ ((p2 ∧ p4) → (True ∧ p6))) ∧ (((True ∨ p5) ∨ (p2 ∧ p2)) → False)) → ((((p0 → False) ∨ (p0 → False)) → ((p2 ∧ p6) ∨ (True → False))) ∧ (((p3 ∧ p4) ∨ (p7 → False)) → ((False → False) ∧ (p3 ∧ p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_12
          case intro assump_15 assump_16 =>
            apply Or.inr
            intro assump_25
            have assump_167 : ((True ∨ p5) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_28 := assump_8 assump_167
            apply False.elim assump_28
  case inr assump_4 =>
    cases assump_1
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_39
          case intro assump_42 assump_43 =>
            apply Or.inr
            intro assump_52
            have assump_168 : ((True ∨ p5) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_55 := assump_35 assump_168
            apply False.elim assump_55
  intro assump_59
  apply And.intro
  intro assump_60
  apply False.elim assump_60
  apply And.intro
  cases assump_59
  case inl assump_63 =>
    cases assump_63
    case intro assump_65 assump_66 =>
      cases assump_1
      case intro assump_71 assump_72 =>
        cases assump_71
        case intro assump_73 assump_74 =>
          cases assump_73
          case intro assump_75 assump_76 =>
            cases assump_76
            case intro assump_79 assump_80 =>
              exact assump_65
  case inr assump_64 =>
    cases assump_1
    case intro assump_91 assump_92 =>
      cases assump_91
      case intro assump_93 assump_94 =>
        cases assump_93
        case intro assump_95 assump_96 =>
          cases assump_96
          case intro assump_99 assump_100 =>
            have assump_169 : ((True ∨ p5) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_109 := assump_92 assump_169
            apply False.elim assump_109
  cases assump_59
  case inl assump_113 =>
    cases assump_113
    case intro assump_115 assump_116 =>
      cases assump_1
      case intro assump_121 assump_122 =>
        cases assump_121
        case intro assump_123 assump_124 =>
          cases assump_123
          case intro assump_125 assump_126 =>
            cases assump_126
            case intro assump_129 assump_130 =>
              have assump_170 : ((True ∨ p5) ∨ (p2 ∧ p2)) := by
                apply Or.inl
                apply Or.inl
                apply True.intro
              let assump_139 := assump_122 assump_170
              apply False.elim assump_139
  case inr assump_114 =>
    cases assump_1
    case intro assump_145 assump_146 =>
      cases assump_145
      case intro assump_147 assump_148 =>
        cases assump_147
        case intro assump_149 assump_150 =>
          cases assump_150
          case intro assump_153 assump_154 =>
            have assump_171 : ((True ∨ p5) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_163 := assump_146 assump_171
            apply False.elim assump_163


variable (p1 p4 p2 p6 p3 : Prop)
theorem file44_107762 : ((((((False ∧ True) → False) ∨ ((False → p1) ∧ (p4 → False))) ∨ (((p2 ∧ p6) → False) → ((True ∨ p3) → (p1 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ True) → False) ∨ ((False → p1) ∧ (p4 → False))) ∨ (((p2 ∧ p6) → False) → ((True ∨ p3) → (p1 ∧ False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p5 p1 : Prop)
theorem file44_108318 : ((((((False ∧ True) → (True → False)) ∨ ((p7 → False) → False)) ∨ (((p1 → False) → (p5 ∨ p1)) → False)) → False) → False) := by
  intro assump_5
  have assump_20 : ((((False ∧ True) → (True → False)) ∨ ((p7 → False) → False)) ∨ (((p1 → False) → (p5 ∨ p1)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_8 := assump_5 assump_20
  apply False.elim assump_8


variable (p6 p2 p7 p1 p0 p3 p5 p4 : Prop)
theorem file44_108884 : (((((p3 → True) → False) ∧ ((p0 ∨ p1) → (p5 → p3))) → (((False → False) ∧ (False → False)) ∨ ((p3 → False) → (p1 → p7)))) ∨ ((((p4 ∧ p5) → (p3 → False)) → ((p2 → True) ∧ (p1 ∧ p2))) ∧ (((p1 → False) ∧ (p1 → False)) ∨ ((p4 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_8
    apply False.elim assump_8
    intro assump_11
    apply False.elim assump_11


variable (p5 p6 p3 p7 : Prop)
theorem file44_109404 : ((((((False → False) → False) → ((p6 → p3) → (p6 ∨ p6))) ∨ (((p5 → False) → False) → ((p7 → False) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → False) → False) → ((p6 → p3) → (p6 ∨ p6))) ∨ (((p5 → False) → False) → ((p7 → False) ∨ (False → False)))) := by
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


variable (p7 p6 p5 p2 p3 p1 : Prop)
theorem file44_110057 : (((((p5 ∨ p6) ∨ (p2 ∧ p6)) → False) → (((True → False) ∧ (p1 → p2)) → ((p5 → p1) ∧ (p6 → True)))) ∨ ((((False → False) ∧ (True → False)) → False) ∨ (((False → False) → (p6 ∧ False)) ∨ ((p7 → True) ∧ (p6 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    have assump_19 : ((p5 ∨ p6) ∨ (p2 ∧ p6)) := by
      apply Or.inl
      apply Or.inl
      exact assump_3
    let assump_14 := assump_1 assump_19
    apply False.elim assump_14
  intro assump_18
  apply True.intro


variable (p7 p1 p2 p5 p6 p0 p4 p3 : Prop)
theorem file44_110695 : (((((True → False) ∧ (p3 ∧ p3)) → False) ∨ (((p3 → False) ∧ (p5 → False)) → ((p2 → p4) → False))) ∨ ((((p3 → False) → False) → ((p6 → False) → (p0 → p1))) ∧ (((p7 ∧ p2) ∨ (False → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_18 : True := by
        apply True.intro
      let assump_14 := assump_2 assump_18
      apply False.elim assump_14


variable (p5 p4 p6 p7 p2 p1 : Prop)
theorem file44_111247 : (((((p5 → False) ∨ (p2 ∨ p5)) ∧ ((p1 → p4) → False)) ∧ (((p1 ∧ p4) → (True ∨ p1)) ∧ ((p7 → False) → (p2 ∧ True)))) → ((((p5 ∧ False) ∧ (p2 → False)) ∧ ((p4 → False) ∨ (p2 → False))) → (((True → False) ∨ (p6 ∧ p1)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
  case inr assump_5 =>
    cases assump_5
    case intro assump_18 assump_19 =>
      cases assump_2
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_29


variable (p5 p6 p4 p0 p1 p7 p2 : Prop)
theorem file44_112167 : (((((True → False) → False) ∨ ((True → False) → (p4 → p2))) ∨ (((True → False) ∧ (p6 ∨ p5)) → False)) ∨ ((((p4 → False) → False) ∨ ((p7 → False) → False)) ∨ (((p4 ∧ True) ∧ (p6 → p2)) ∧ ((p5 → p5) ∧ (p1 → p0))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_5
  have assump_12 : True := by
    apply True.intro
  let assump_8 := assump_5 assump_12
  apply False.elim assump_8


variable (p6 p5 p7 p4 p2 p0 p1 : Prop)
theorem file44_112627 : (((((p1 ∨ p1) ∨ (False → True)) → ((p2 ∨ p6) ∨ (p0 → True))) ∨ (((p6 → p2) → (p2 → p4)) ∨ ((False → False) → (p7 ∧ p7)))) ∨ ((((p4 ∨ p7) → False) ∨ ((p7 ∧ p7) → False)) ∨ (((True → p4) ∨ (p6 → False)) → ((p2 ∨ p0) ∨ (p5 → p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_8
      apply True.intro
    case inr assump_5 =>
      apply Or.inr
      intro assump_11
      apply True.intro
  case inr assump_3 =>
    apply Or.inr
    intro assump_14
    apply True.intro


variable (p1 p5 p3 p4 p6 p7 p0 : Prop)
theorem file44_113290 : (((((p5 → False) ∧ (p5 ∨ p3)) ∧ ((True ∧ False) ∧ (p0 ∨ p1))) → (((p5 ∨ p3) → False) → False)) ∨ ((((False → False) → (p5 → p4)) ∧ ((p3 ∨ p5) → False)) ∧ (((p7 → p4) → False) ∧ ((True → False) → (p0 → p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
      case inr assump_12 =>
        cases assump_6
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            apply False.elim assump_28


variable (p7 p0 p6 p4 p1 p2 p3 : Prop)
theorem file44_114148 : (((((p7 → False) ∧ (p4 → False)) → ((p2 → p2) → (p7 → False))) ∨ (((p1 → p6) → False) → False)) ∨ ((((p4 ∧ p3) ∨ (False ∨ p3)) ∨ ((p7 → p6) ∧ (p0 ∧ p1))) → (((p4 → p4) → False) ∨ ((p1 → False) → (p4 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    have assump_19 : p7 := by
      exact assump_3
    let assump_15 := assump_8 assump_19
    apply False.elim assump_15


variable (p7 p4 p1 p5 : Prop)
theorem file44_114674 : (((((p1 → True) → False) → ((p5 → p4) ∧ (False ∧ p7))) → False) → False) := by
  intro assump_1
  have assump_33 : (((p1 → True) → False) → ((p5 → p4) ∧ (False ∧ p7))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_34 : (p1 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_5 assump_34
    apply False.elim assump_11
    apply And.intro
    have assump_35 : (p1 → True) := by
      intro assump_19
      apply True.intro
    let assump_18 := assump_5 assump_35
    apply False.elim assump_18
    have assump_36 : (p1 → True) := by
      intro assump_26
      apply True.intro
    let assump_25 := assump_5 assump_36
    apply False.elim assump_25
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p2 p7 p3 p1 p6 p0 : Prop)
theorem file44_115516 : (((((False → p7) → False) → ((p2 → False) → False)) ∨ (((p1 → True) ∧ (False ∧ p0)) → ((p7 → False) ∨ (p7 ∧ p1)))) ∨ ((((p6 ∨ p6) ∨ (True ∨ p3)) ∨ ((False → False) → False)) ∨ (((p1 ∨ p3) → (p3 → False)) ∧ ((False → p6) ∧ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_14 : (False → p7) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p5 p2 p0 p7 p4 p3 p1 p6 : Prop)
theorem file44_116043 : (((((p5 → p6) → (p0 ∨ p5)) → False) ∧ (((p5 ∧ p4) ∨ (p0 ∧ p2)) ∧ ((p5 ∨ p5) ∧ (p6 → False)))) → ((((p3 → False) ∧ (p1 ∧ p3)) → False) ∨ (((p2 → False) ∧ (p7 → p6)) ∧ ((p2 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              apply Or.inl
              intro assump_24
              cases assump_24
              case intro assump_25 assump_26 =>
                cases assump_26
                case intro assump_29 assump_30 =>
                  have assump_114 : p3 := by
                    exact assump_30
                  let assump_37 := assump_25 assump_114
                  apply False.elim assump_37
            case inr assump_19 =>
              apply Or.inl
              intro assump_45
              cases assump_45
              case intro assump_46 assump_47 =>
                cases assump_47
                case intro assump_50 assump_51 =>
                  have assump_115 : p3 := by
                    exact assump_51
                  let assump_58 := assump_46 assump_115
                  apply False.elim assump_58
      case inr assump_9 =>
        cases assump_9
        case intro assump_62 assump_63 =>
          cases assump_7
          case intro assump_68 assump_69 =>
            cases assump_68
            case inl assump_70 =>
              apply Or.inl
              intro assump_76
              cases assump_76
              case intro assump_77 assump_78 =>
                cases assump_78
                case intro assump_81 assump_82 =>
                  have assump_116 : p3 := by
                    exact assump_82
                  let assump_89 := assump_77 assump_116
                  apply False.elim assump_89
            case inr assump_71 =>
              apply Or.inl
              intro assump_97
              cases assump_97
              case intro assump_98 assump_99 =>
                cases assump_99
                case intro assump_102 assump_103 =>
                  have assump_117 : p3 := by
                    exact assump_103
                  let assump_110 := assump_98 assump_117
                  apply False.elim assump_110


variable (p3 p0 p5 p2 p7 p1 p6 : Prop)
theorem file44_118563 : ((((((p3 → p6) → (p1 ∨ p0)) ∧ ((True → False) ∨ (True → True))) → False) ∧ ((((p6 ∨ p5) ∨ (p6 ∨ p7)) → ((p2 → False) → (False → p7))) ∧ (((False ∨ p1) → (p1 ∨ p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((False ∨ p1) → (p1 ∨ p2)) := by
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply Or.inl
          exact assump_15
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p1 p7 p5 p0 p6 p2 p3 : Prop)
theorem file44_119264 : (((((False → False) → False) → ((p1 → p5) ∨ (p6 ∨ p0))) ∨ (((p0 → False) ∨ (False ∨ p0)) → ((p1 ∨ p7) → (p7 ∨ p7)))) ∨ ((((p0 → False) → False) ∧ ((p5 ∧ p0) → (p6 ∧ p0))) → (((p3 → p5) → (p2 ∨ True)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_15 : (False → False) := by
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p6 p4 p1 p3 p0 p2 p5 : Prop)
theorem file44_119778 : ((((((p6 → p1) → (p0 ∧ p2)) ∨ ((True → False) ∨ (p6 ∨ p5))) ∨ (((p6 → p0) ∨ (p6 ∧ p0)) → False)) ∧ ((((True → False) ∨ (False ∧ p0)) → ((p4 → False) → False)) → (((p5 → False) → (p5 → p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_187 : (((True → False) ∨ (False ∧ p0)) → ((p4 → False) → False)) := by
          intro assump_13
          intro assump_14
          cases assump_13
          case inl assump_17 =>
            have assump_188 : True := by
              apply True.intro
            let assump_21 := assump_17 assump_188
            apply False.elim assump_21
          case inr assump_18 =>
            cases assump_18
            case intro assump_25 assump_26 =>
              apply False.elim assump_25
        let assump_12 := assump_3 assump_187
        have assump_189 : ((p5 → False) → (p5 → p3)) := by
          intro assump_30
          intro assump_31
          have assump_190 : p5 := by
            exact assump_31
          let assump_36 := assump_30 assump_190
          apply False.elim assump_36
        let assump_29 := assump_12 assump_189
        apply False.elim assump_29
      case inr assump_7 =>
        cases assump_7
        case inl assump_43 =>
          have assump_191 : (((True → False) ∨ (False ∧ p0)) → ((p4 → False) → False)) := by
            intro assump_50
            intro assump_51
            cases assump_50
            case inl assump_54 =>
              have assump_192 : True := by
                apply True.intro
              let assump_58 := assump_54 assump_192
              apply False.elim assump_58
            case inr assump_55 =>
              cases assump_55
              case intro assump_62 assump_63 =>
                apply False.elim assump_62
          let assump_49 := assump_3 assump_191
          have assump_193 : ((p5 → False) → (p5 → p3)) := by
            intro assump_67
            intro assump_68
            have assump_194 : p5 := by
              exact assump_68
            let assump_73 := assump_67 assump_194
            apply False.elim assump_73
          let assump_66 := assump_49 assump_193
          apply False.elim assump_66
        case inr assump_44 =>
          cases assump_44
          case inl assump_80 =>
            have assump_195 : (((True → False) ∨ (False ∧ p0)) → ((p4 → False) → False)) := by
              intro assump_87
              intro assump_88
              cases assump_87
              case inl assump_91 =>
                have assump_196 : True := by
                  apply True.intro
                let assump_95 := assump_91 assump_196
                apply False.elim assump_95
              case inr assump_92 =>
                cases assump_92
                case intro assump_99 assump_100 =>
                  apply False.elim assump_99
            let assump_86 := assump_3 assump_195
            have assump_197 : ((p5 → False) → (p5 → p3)) := by
              intro assump_104
              intro assump_105
              have assump_198 : p5 := by
                exact assump_105
              let assump_110 := assump_104 assump_198
              apply False.elim assump_110
            let assump_103 := assump_86 assump_197
            apply False.elim assump_103
          case inr assump_81 =>
            have assump_199 : (((True → False) ∨ (False ∧ p0)) → ((p4 → False) → False)) := by
              intro assump_122
              intro assump_123
              cases assump_122
              case inl assump_126 =>
                have assump_200 : True := by
                  apply True.intro
                let assump_130 := assump_126 assump_200
                apply False.elim assump_130
              case inr assump_127 =>
                cases assump_127
                case intro assump_134 assump_135 =>
                  apply False.elim assump_134
            let assump_121 := assump_3 assump_199
            have assump_201 : ((p5 → False) → (p5 → p3)) := by
              intro assump_139
              intro assump_140
              have assump_202 : p5 := by
                exact assump_140
              let assump_145 := assump_139 assump_202
              apply False.elim assump_145
            let assump_138 := assump_121 assump_201
            apply False.elim assump_138
    case inr assump_5 =>
      have assump_203 : (((True → False) ∨ (False ∧ p0)) → ((p4 → False) → False)) := by
        intro assump_157
        intro assump_158
        cases assump_157
        case inl assump_161 =>
          have assump_204 : True := by
            apply True.intro
          let assump_165 := assump_161 assump_204
          apply False.elim assump_165
        case inr assump_162 =>
          cases assump_162
          case intro assump_169 assump_170 =>
            apply False.elim assump_169
      let assump_156 := assump_3 assump_203
      have assump_205 : ((p5 → False) → (p5 → p3)) := by
        intro assump_174
        intro assump_175
        have assump_206 : p5 := by
          exact assump_175
        let assump_180 := assump_174 assump_206
        apply False.elim assump_180
      let assump_173 := assump_156 assump_205
      apply False.elim assump_173


variable (p1 p7 : Prop)
theorem file44_125143 : (((((p1 ∧ p1) ∧ (p1 ∧ False)) → ((p7 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : (((p1 ∧ p1) ∧ (p1 ∧ False)) → ((p7 → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


