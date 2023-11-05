variable (p2 p6 p4 p0 p7 p3 p5 p1 : Prop)
theorem file55_50 : ((((((True → False) → (p3 ∨ p7)) → ((p1 → False) → False)) ∧ (((False ∧ p4) ∨ (p4 ∧ True)) ∧ ((False → False) ∧ (False ∧ p2)))) ∧ ((((p5 ∨ p5) → (p0 ∨ p0)) ∨ ((True → p2) → (p7 ∧ p0))) ∧ (((p0 ∨ True) ∧ (False ∨ p6)) ∨ ((p4 ∧ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
        case inr assump_11 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            cases assump_9
            case intro assump_22 assump_23 =>
              cases assump_23
              case intro assump_26 assump_27 =>
                apply False.elim assump_26


variable (p0 p3 p7 p6 : Prop)
theorem file55_999 : ((((((p7 ∨ p7) ∧ (p6 ∧ p3)) ∧ ((p7 → False) ∨ (p0 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_59 : ((((p7 ∨ p7) ∧ (p6 ∧ p3)) ∧ ((p7 → False) ∨ (p0 ∧ False))) → False) := by
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
            case inl assump_20 =>
              have assump_60 : p7 := by
                exact assump_10
              let assump_24 := assump_20 assump_60
              apply False.elim assump_24
            case inr assump_21 =>
              cases assump_21
              case intro assump_28 assump_29 =>
                apply False.elim assump_29
        case inr assump_11 =>
          cases assump_9
          case intro assump_36 assump_37 =>
            cases assump_7
            case inl assump_42 =>
              have assump_61 : p7 := by
                exact assump_11
              let assump_46 := assump_42 assump_61
              apply False.elim assump_46
            case inr assump_43 =>
              cases assump_43
              case intro assump_50 assump_51 =>
                apply False.elim assump_51
  let assump_4 := assump_1 assump_59
  apply False.elim assump_4


variable (p0 p2 p7 p1 p5 p3 p6 : Prop)
theorem file55_2445 : (((((p3 ∨ p5) ∨ (p1 → p3)) → ((p1 ∨ p0) ∨ (p5 ∨ p6))) → False) → ((((p0 ∨ True) → (p2 → p2)) ∨ ((p3 ∧ p7) ∧ (p6 → p2))) ∨ (((p3 ∧ p0) → (p0 → p5)) → ((p2 ∨ True) → (False ∨ p3))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    exact assump_5
  case inr assump_9 =>
    exact assump_5


variable (p2 p6 p0 p7 p3 p5 : Prop)
theorem file55_2874 : ((((((p3 ∧ True) ∧ (p6 ∨ p7)) → False) → (((p6 → False) → (p2 → p0)) → ((p6 → True) → (p5 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p3 ∧ True) ∧ (p6 ∨ p7)) → False) → (((p6 → False) → (p2 → p0)) → ((p6 → True) → (p5 → True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p2 p6 p4 p3 p1 : Prop)
theorem file55_3362 : (((((p2 ∧ False) ∨ (False ∧ p5)) → False) ∧ (((p3 → False) → (True ∨ p1)) ∨ ((p1 ∧ p1) → (p4 → p5)))) ∧ ((((p2 → p2) ∨ (p6 ∧ p6)) → False) → False)) := by
  apply And.intro
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5
  case inr assump_3 =>
    cases assump_3
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  apply Or.inl
  intro assump_14
  apply Or.inl
  apply True.intro
  intro assump_17
  have assump_27 : ((p2 → p2) ∨ (p6 ∧ p6)) := by
    apply Or.inl
    intro assump_21
    exact assump_21
  let assump_20 := assump_17 assump_27
  apply False.elim assump_20


variable (p6 p7 p4 p3 p2 p1 : Prop)
theorem file55_4129 : (((((p3 ∨ p4) ∧ (p4 ∧ False)) → ((p7 ∧ p1) → False)) ∨ (((False → p4) ∧ (True → p4)) → ((p7 ∧ p1) → (p1 → False)))) ∨ ((((p2 → p3) ∧ (p1 → p6)) → ((p4 → False) → False)) ∧ (((p4 → p1) ∧ (p6 → False)) ∧ ((p2 ∨ p2) → False)))) := by
  apply Or.inl
  apply Or.inl
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
          apply False.elim assump_16
      case inr assump_12 =>
        cases assump_10
        case intro assump_23 assump_24 =>
          apply False.elim assump_24


variable (p0 p5 p3 p7 p4 p2 p6 : Prop)
theorem file55_4877 : (((((False → True) ∧ (p4 → p5)) ∧ ((p0 ∨ p4) ∧ (p7 ∨ False))) ∧ (((p5 → p5) → (True ∨ p2)) ∧ ((p7 ∨ p2) → False))) → ((((p4 → False) → (p6 → p3)) ∧ ((p5 → False) ∧ (p6 → False))) ∧ (((p4 → False) ∨ (p3 → False)) ∧ ((p3 ∨ p2) → (p6 ∨ p3))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_19
            case inl assump_24 =>
              cases assump_9
              case intro assump_28 assump_29 =>
                have assump_321 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_24
                let assump_34 := assump_29 assump_321
                apply False.elim assump_34
            case inr assump_25 =>
              apply False.elim assump_25
          case inr assump_21 =>
            cases assump_19
            case inl assump_42 =>
              cases assump_9
              case intro assump_46 assump_47 =>
                have assump_322 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_42
                let assump_52 := assump_47 assump_322
                apply False.elim assump_52
            case inr assump_43 =>
              apply False.elim assump_43
  apply And.intro
  intro assump_58
  cases assump_1
  case intro assump_61 assump_62 =>
    cases assump_61
    case intro assump_63 assump_64 =>
      cases assump_63
      case intro assump_65 assump_66 =>
        cases assump_64
        case intro assump_71 assump_72 =>
          cases assump_71
          case inl assump_73 =>
            cases assump_72
            case inl assump_77 =>
              cases assump_62
              case intro assump_81 assump_82 =>
                have assump_323 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_77
                let assump_87 := assump_82 assump_323
                apply False.elim assump_87
            case inr assump_78 =>
              apply False.elim assump_78
          case inr assump_74 =>
            cases assump_72
            case inl assump_95 =>
              cases assump_62
              case intro assump_99 assump_100 =>
                have assump_324 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_95
                let assump_105 := assump_100 assump_324
                apply False.elim assump_105
            case inr assump_96 =>
              apply False.elim assump_96
  intro assump_111
  cases assump_1
  case intro assump_114 assump_115 =>
    cases assump_114
    case intro assump_116 assump_117 =>
      cases assump_116
      case intro assump_118 assump_119 =>
        cases assump_117
        case intro assump_124 assump_125 =>
          cases assump_124
          case inl assump_126 =>
            cases assump_125
            case inl assump_130 =>
              cases assump_115
              case intro assump_134 assump_135 =>
                have assump_325 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_130
                let assump_140 := assump_135 assump_325
                apply False.elim assump_140
            case inr assump_131 =>
              apply False.elim assump_131
          case inr assump_127 =>
            cases assump_125
            case inl assump_148 =>
              cases assump_115
              case intro assump_152 assump_153 =>
                have assump_326 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_148
                let assump_158 := assump_153 assump_326
                apply False.elim assump_158
            case inr assump_149 =>
              apply False.elim assump_149
  apply And.intro
  cases assump_1
  case intro assump_164 assump_165 =>
    cases assump_164
    case intro assump_166 assump_167 =>
      cases assump_166
      case intro assump_168 assump_169 =>
        cases assump_167
        case intro assump_174 assump_175 =>
          cases assump_174
          case inl assump_176 =>
            cases assump_175
            case inl assump_180 =>
              cases assump_165
              case intro assump_184 assump_185 =>
                apply Or.inl
                intro assump_190
                have assump_327 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_180
                let assump_194 := assump_185 assump_327
                apply False.elim assump_194
            case inr assump_181 =>
              apply False.elim assump_181
          case inr assump_177 =>
            cases assump_175
            case inl assump_202 =>
              cases assump_165
              case intro assump_206 assump_207 =>
                apply Or.inl
                intro assump_212
                have assump_328 : (p7 ∨ p2) := by
                  apply Or.inl
                  exact assump_202
                let assump_216 := assump_207 assump_328
                apply False.elim assump_216
            case inr assump_203 =>
              apply False.elim assump_203
  intro assump_222
  cases assump_222
  case inl assump_223 =>
    cases assump_1
    case intro assump_227 assump_228 =>
      cases assump_227
      case intro assump_229 assump_230 =>
        cases assump_229
        case intro assump_231 assump_232 =>
          cases assump_230
          case intro assump_237 assump_238 =>
            cases assump_237
            case inl assump_239 =>
              cases assump_238
              case inl assump_243 =>
                cases assump_228
                case intro assump_247 assump_248 =>
                  apply Or.inr
                  exact assump_223
              case inr assump_244 =>
                apply False.elim assump_244
            case inr assump_240 =>
              cases assump_238
              case inl assump_257 =>
                cases assump_228
                case intro assump_261 assump_262 =>
                  apply Or.inr
                  exact assump_223
              case inr assump_258 =>
                apply False.elim assump_258
  case inr assump_224 =>
    cases assump_1
    case intro assump_271 assump_272 =>
      cases assump_271
      case intro assump_273 assump_274 =>
        cases assump_273
        case intro assump_275 assump_276 =>
          cases assump_274
          case intro assump_281 assump_282 =>
            cases assump_281
            case inl assump_283 =>
              cases assump_282
              case inl assump_287 =>
                cases assump_272
                case intro assump_291 assump_292 =>
                  have assump_329 : (p7 ∨ p2) := by
                    apply Or.inl
                    exact assump_287
                  let assump_297 := assump_292 assump_329
                  apply False.elim assump_297
              case inr assump_288 =>
                apply False.elim assump_288
            case inr assump_284 =>
              cases assump_282
              case inl assump_305 =>
                cases assump_272
                case intro assump_309 assump_310 =>
                  have assump_330 : (p7 ∨ p2) := by
                    apply Or.inl
                    exact assump_305
                  let assump_315 := assump_310 assump_330
                  apply False.elim assump_315
              case inr assump_306 =>
                apply False.elim assump_306


variable (p5 p3 p2 p1 p0 p4 p7 p6 : Prop)
theorem file55_12615 : ((((((p0 ∨ p2) → (True → p5)) ∧ ((False ∧ p3) ∧ (p6 ∧ p0))) ∧ (((False → False) → (p5 → False)) → ((p0 ∧ p4) → (p1 → False)))) ∧ ((((p7 ∧ p7) ∧ (p0 → False)) ∨ ((True ∨ p2) ∧ (p0 → p0))) ∧ (((p6 → False) → False) → ((False ∧ p5) ∨ (p6 → False))))) → False) := by
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
          case intro assump_12 assump_13 =>
            apply False.elim assump_12


variable (p7 p0 p2 p5 : Prop)
theorem file55_13288 : ((((((False → False) ∧ (p7 ∧ False)) ∨ ((p2 ∧ False) ∧ (False ∧ False))) ∧ (((p5 ∨ p2) → False) → False)) ∧ ((((p5 ∧ p7) → (p2 ∧ False)) ∧ ((p2 ∧ p5) ∨ (p0 → False))) → False)) → False) := by
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
            apply False.elim assump_13
      case inr assump_7 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_21


variable (p3 p5 p0 : Prop)
theorem file55_14074 : ((((((p0 → p5) → (True ∨ p3)) → False) → False) → False) → False) := by
  intro assump_7
  have assump_24 : ((((p0 → p5) → (True ∨ p3)) → False) → False) := by
    intro assump_11
    have assump_25 : ((p0 → p5) → (True ∨ p3)) := by
      intro assump_15
      apply Or.inl
      apply True.intro
    let assump_14 := assump_11 assump_25
    apply False.elim assump_14
  let assump_10 := assump_7 assump_24
  apply False.elim assump_10


variable (p1 p2 p5 p3 p0 p7 p4 : Prop)
theorem file55_14573 : ((((((p1 → p5) → (p1 → False)) ∨ ((p2 → p3) → False)) ∧ (((p3 ∨ p1) → False) ∧ ((p5 → False) ∧ (p5 → False)))) ∧ ((((p0 → False) → (p3 → False)) → ((p7 ∨ p4) ∨ (False → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            have assump_56 : (((p0 → False) → (p3 → False)) → ((p7 ∨ p4) ∨ (False → p7))) := by
              intro assump_23
              apply Or.inr
              intro assump_26
              apply False.elim assump_26
            let assump_22 := assump_3 assump_56
            apply False.elim assump_22
      case inr assump_7 =>
        cases assump_5
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            have assump_57 : (((p0 → False) → (p3 → False)) → ((p7 ∨ p4) ∨ (False → p7))) := by
              intro assump_47
              apply Or.inr
              intro assump_50
              apply False.elim assump_50
            let assump_46 := assump_3 assump_57
            apply False.elim assump_46


variable (p0 p1 p6 p4 p2 p3 p7 : Prop)
theorem file55_15926 : (((((p6 ∨ False) ∧ (p6 ∧ p2)) → False) → (((p4 → p4) ∨ (False → p7)) ∨ ((p4 ∧ p2) → (p0 ∧ p6)))) ∨ ((((p3 → p2) → False) ∨ ((p4 → False) ∧ (p2 ∨ p1))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  exact assump_4


variable (p3 p0 p4 p7 p1 p2 : Prop)
theorem file55_16249 : (((((p2 → False) → (p0 → True)) ∧ ((p1 ∨ p7) ∧ (False ∧ p3))) → False) ∨ ((((False → p7) → False) → ((p7 → False) ∨ (p4 → False))) ∨ (((p1 → p3) → (p2 ∧ p0)) → ((p2 ∨ p2) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
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


variable (p0 p3 p2 p6 p7 p1 : Prop)
theorem file55_16915 : (((((p6 ∨ p6) ∨ (p0 ∧ p2)) → ((p2 ∨ p7) → False)) → (((False ∧ True) → False) ∨ ((p6 ∧ p3) → False))) ∨ ((((p2 ∧ True) ∧ (p3 → False)) ∧ ((p1 ∨ False) → False)) → (((p7 ∧ p1) → (p2 ∨ True)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p2 p3 p5 p0 p1 : Prop)
theorem file55_17324 : (((((False ∨ p1) ∨ (False ∨ p3)) ∧ ((p5 ∨ True) ∧ (True ∨ False))) → (((p0 ∨ p3) ∧ (p3 → False)) → ((True → False) → False))) ∨ ((((p5 ∧ False) → (p2 → p3)) → False) ∨ (((p1 → False) ∨ (p3 → p5)) ∨ ((True ∧ True) ∨ (p5 → False))))) := by
  apply Or.inl
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_8
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_7
      case intro assump_20 assump_21 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_22
          case inl assump_24 =>
            apply False.elim assump_24
          case inr assump_25 =>
            cases assump_21
            case intro assump_30 assump_31 =>
              cases assump_30
              case inl assump_32 =>
                cases assump_31
                case inl assump_36 =>
                  have assump_184 : True := by
                    apply True.intro
                  let assump_44 := assump_9 assump_184
                  apply False.elim assump_44
                case inr assump_37 =>
                  apply False.elim assump_37
              case inr assump_33 =>
                cases assump_31
                case inl assump_52 =>
                  have assump_185 : True := by
                    apply True.intro
                  let assump_59 := assump_9 assump_185
                  apply False.elim assump_59
                case inr assump_53 =>
                  apply False.elim assump_53
        case inr assump_23 =>
          cases assump_23
          case inl assump_65 =>
            apply False.elim assump_65
          case inr assump_66 =>
            cases assump_21
            case intro assump_71 assump_72 =>
              cases assump_71
              case inl assump_73 =>
                cases assump_72
                case inl assump_77 =>
                  have assump_186 : p3 := by
                    exact assump_66
                  let assump_83 := assump_13 assump_186
                  apply False.elim assump_83
                case inr assump_78 =>
                  apply False.elim assump_78
              case inr assump_74 =>
                cases assump_72
                case inl assump_91 =>
                  have assump_187 : p3 := by
                    exact assump_66
                  let assump_96 := assump_13 assump_187
                  apply False.elim assump_96
                case inr assump_92 =>
                  apply False.elim assump_92
    case inr assump_15 =>
      cases assump_7
      case intro assump_106 assump_107 =>
        cases assump_106
        case inl assump_108 =>
          cases assump_108
          case inl assump_110 =>
            apply False.elim assump_110
          case inr assump_111 =>
            cases assump_107
            case intro assump_116 assump_117 =>
              cases assump_116
              case inl assump_118 =>
                cases assump_117
                case inl assump_122 =>
                  have assump_188 : p3 := by
                    exact assump_15
                  let assump_128 := assump_13 assump_188
                  apply False.elim assump_128
                case inr assump_123 =>
                  apply False.elim assump_123
              case inr assump_119 =>
                cases assump_117
                case inl assump_136 =>
                  have assump_189 : p3 := by
                    exact assump_15
                  let assump_141 := assump_13 assump_189
                  apply False.elim assump_141
                case inr assump_137 =>
                  apply False.elim assump_137
        case inr assump_109 =>
          cases assump_109
          case inl assump_147 =>
            apply False.elim assump_147
          case inr assump_148 =>
            cases assump_107
            case intro assump_153 assump_154 =>
              cases assump_153
              case inl assump_155 =>
                cases assump_154
                case inl assump_159 =>
                  have assump_190 : p3 := by
                    exact assump_148
                  let assump_165 := assump_13 assump_190
                  apply False.elim assump_165
                case inr assump_160 =>
                  apply False.elim assump_160
              case inr assump_156 =>
                cases assump_154
                case inl assump_173 =>
                  have assump_191 : p3 := by
                    exact assump_148
                  let assump_178 := assump_13 assump_191
                  apply False.elim assump_178
                case inr assump_174 =>
                  apply False.elim assump_174


variable (p1 p7 p5 p2 p3 p4 : Prop)
theorem file55_22058 : ((((((p5 ∨ p1) → (p7 → False)) ∧ ((p4 → True) → False)) → (((False ∧ True) ∨ (p3 → p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p5 ∨ p1) → (p7 → False)) ∧ ((p4 → True) → False)) → (((False ∧ True) ∨ (p3 → p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_8 =>
      cases assump_5
      case intro assump_15 assump_16 =>
        have assump_30 : (p4 → True) := by
          intro assump_22
          apply True.intro
        let assump_21 := assump_16 assump_30
        apply False.elim assump_21
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p3 p0 p7 p5 p2 : Prop)
theorem file55_22881 : (((((p1 ∧ p1) ∧ (p5 → p5)) → ((p7 ∨ p1) → (p5 → p2))) ∧ (((True ∨ p2) ∨ (p5 ∨ p7)) → False)) → ((((p7 → False) ∨ (True ∧ p2)) → False) ∨ (((p3 ∨ p5) → (p0 ∧ p1)) ∨ ((p7 → False) → False)))) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    apply Or.inl
    intro assump_19
    cases assump_19
    case inl assump_20 =>
      have assump_40 : ((True ∨ p2) ∨ (p5 ∨ p7)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_25 := assump_14 assump_40
      apply False.elim assump_25
    case inr assump_21 =>
      cases assump_21
      case intro assump_29 assump_30 =>
        have assump_41 : ((True ∨ p2) ∨ (p5 ∨ p7)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_36 := assump_14 assump_41
        apply False.elim assump_36


variable (p2 p1 p3 : Prop)
theorem file55_23779 : ((((((True → False) ∧ (p1 → p2)) → False) ∨ (((p3 → False) ∨ (p3 → False)) → ((p1 ∧ p1) ∨ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((True → False) ∧ (p1 → p2)) → False) ∨ (((p3 → False) ∨ (p3 → False)) → ((p1 ∧ p1) ∨ (p1 → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p5 p2 p3 p1 p6 : Prop)
theorem file55_24402 : (((((p6 → False) → False) → ((p3 ∨ True) ∨ (p1 ∧ False))) ∨ (((False → p5) ∧ (True → True)) ∧ ((p2 ∧ p2) → (p5 → False)))) ∨ ((((False ∧ p3) ∨ (p1 ∧ p1)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p5 p6 p3 p4 p0 p7 : Prop)
theorem file55_24737 : ((((((p6 → p3) ∨ (p5 → False)) ∨ ((True → False) ∨ (p5 ∧ p0))) ∨ (((True → p7) → False) → False)) ∧ ((((p4 ∧ p4) → False) → ((False → False) ∧ (p7 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_81 : (((p4 ∧ p4) → False) → ((False → False) ∧ (p7 → True))) := by
            intro assump_15
            apply And.intro
            intro assump_16
            apply False.elim assump_16
            intro assump_19
            apply True.intro
          let assump_14 := assump_3 assump_81
          apply False.elim assump_14
        case inr assump_9 =>
          have assump_82 : (((p4 ∧ p4) → False) → ((False → False) ∧ (p7 → True))) := by
            intro assump_28
            apply And.intro
            intro assump_29
            apply False.elim assump_29
            intro assump_32
            apply True.intro
          let assump_27 := assump_3 assump_82
          apply False.elim assump_27
      case inr assump_7 =>
        cases assump_7
        case inl assump_36 =>
          have assump_83 : (((p4 ∧ p4) → False) → ((False → False) ∧ (p7 → True))) := by
            intro assump_43
            apply And.intro
            intro assump_44
            apply False.elim assump_44
            intro assump_47
            apply True.intro
          let assump_42 := assump_3 assump_83
          apply False.elim assump_42
        case inr assump_37 =>
          cases assump_37
          case intro assump_51 assump_52 =>
            have assump_84 : (((p4 ∧ p4) → False) → ((False → False) ∧ (p7 → True))) := by
              intro assump_60
              apply And.intro
              intro assump_61
              apply False.elim assump_61
              intro assump_64
              apply True.intro
            let assump_59 := assump_3 assump_84
            apply False.elim assump_59
    case inr assump_5 =>
      have assump_85 : (((p4 ∧ p4) → False) → ((False → False) ∧ (p7 → True))) := by
        intro assump_73
        apply And.intro
        intro assump_74
        apply False.elim assump_74
        intro assump_77
        apply True.intro
      let assump_72 := assump_3 assump_85
      apply False.elim assump_72


variable (p4 p7 p5 p0 p3 p6 : Prop)
theorem file55_27167 : (((((p5 → False) → False) ∨ ((p4 ∧ p6) → False)) ∧ (((p0 → False) → False) → False)) → ((((p0 ∨ p6) → (p3 → p7)) ∧ ((p6 → p7) ∧ (True ∧ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            have assump_51 : ((p0 → False) → False) := by
              intro assump_26
              have assump_52 : p0 := by
                exact assump_12
              let assump_29 := assump_26 assump_52
              apply False.elim assump_29
            let assump_25 := assump_18 assump_51
            apply False.elim assump_25
          case inr assump_20 =>
            have assump_53 : ((p0 → False) → False) := by
              intro assump_41
              have assump_54 : p0 := by
                exact assump_12
              let assump_44 := assump_41 assump_54
              apply False.elim assump_44
            let assump_40 := assump_18 assump_53
            apply False.elim assump_40


variable (p0 p5 p3 p4 p1 p2 p6 p7 : Prop)
theorem file55_28427 : (((((p0 → p2) ∨ (False → p1)) → ((p4 → p4) ∨ (True ∨ p5))) ∨ (((p5 → False) → False) → False)) ∨ ((((p6 → p0) → (p4 → True)) ∧ ((p4 → False) → (p0 ∨ p3))) ∧ (((p0 ∨ p7) ∨ (p5 → p6)) ∨ ((p6 → p7) → (p6 ∨ p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    exact assump_6
  case inr assump_3 =>
    apply Or.inl
    intro assump_11
    exact assump_11


variable (p3 p2 p1 p5 p7 p6 p0 p4 : Prop)
theorem file55_28932 : (((((p4 → False) ∨ (p1 → False)) → ((p1 ∧ p7) ∨ (p0 ∨ p3))) → False) → ((((False ∧ p5) ∧ (p2 ∧ p3)) ∨ ((False ∧ p4) ∧ (p7 → False))) ∨ (((p6 ∧ p2) → (False → p7)) → ((p1 ∧ p0) → (True ∧ p5))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  apply And.intro
  apply True.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_28 : (((p4 → False) ∨ (p1 → False)) → ((p1 ∧ p7) ∨ (p0 ∨ p3))) := by
      intro assump_18
      cases assump_18
      case inl assump_19 =>
        apply Or.inr
        apply Or.inl
        exact assump_7
      case inr assump_20 =>
        apply Or.inr
        apply Or.inl
        exact assump_7
    let assump_17 := assump_1 assump_28
    apply False.elim assump_17


variable (p2 p3 p4 p7 p0 p1 p6 p5 : Prop)
theorem file55_29738 : ((((((p1 ∨ p0) ∨ (True → p3)) ∧ ((False ∧ p6) → (True ∧ p3))) → (((p7 ∧ p2) ∧ (p4 ∧ True)) ∨ ((False ∨ False) → False))) → ((((p7 → p6) ∧ (False ∧ False)) ∧ ((True ∧ False) → (p5 → False))) ∧ (((p3 → False) ∨ (p4 → False)) → False))) → False) := by
  intro assump_1
  have assump_53 : ((((p1 ∨ p0) ∨ (True → p3)) ∧ ((False ∧ p6) → (True ∧ p3))) → (((p7 ∧ p2) ∧ (p4 ∧ True)) ∨ ((False ∨ False) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inr
          intro assump_16
          cases assump_16
          case inl assump_17 =>
            apply False.elim assump_17
          case inr assump_18 =>
            apply False.elim assump_18
        case inr assump_11 =>
          apply Or.inr
          intro assump_27
          cases assump_27
          case inl assump_28 =>
            apply False.elim assump_28
          case inr assump_29 =>
            apply False.elim assump_29
      case inr assump_9 =>
        apply Or.inr
        intro assump_38
        cases assump_38
        case inl assump_39 =>
          apply False.elim assump_39
        case inr assump_40 =>
          apply False.elim assump_40
  let assump_4 := assump_1 assump_53
  let assump_45 := And.left assump_4
  let assump_46 := And.left assump_45
  let assump_47 := And.right assump_46
  let assump_49 := And.left assump_47
  apply False.elim assump_49


variable (p3 p2 p7 : Prop)
theorem file55_31286 : (((((p2 ∧ True) ∨ (True ∨ False)) → False) ∧ (((p2 → False) ∧ (p7 ∧ p2)) ∨ ((p7 → False) ∧ (p3 → False)))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_16
    case inl assump_19 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          have assump_49 : p2 := by
            exact assump_26
          let assump_33 := assump_21 assump_49
          apply False.elim assump_33
    case inr assump_20 =>
      cases assump_20
      case intro assump_37 assump_38 =>
        have assump_50 : ((p2 ∧ True) ∨ (True ∨ False)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_45 := assump_15 assump_50
        apply False.elim assump_45


variable (p4 p6 p1 p3 p5 p2 : Prop)
theorem file55_32165 : (((((p4 → p5) ∧ (False → p4)) ∧ ((p6 → p2) ∧ (p3 ∨ False))) ∧ (((True ∧ p2) → False) ∧ ((p6 ∨ False) ∧ (p3 → False)))) → ((((True → False) → (True → False)) → ((p5 ∧ p1) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            cases assump_6
            case intro assump_23 assump_24 =>
              cases assump_24
              case intro assump_27 assump_28 =>
                cases assump_27
                case inl assump_29 =>
                  have assump_43 : p3 := by
                    exact assump_19
                  let assump_35 := assump_28 assump_43
                  apply False.elim assump_35
                case inr assump_30 =>
                  apply False.elim assump_30
          case inr assump_20 =>
            apply False.elim assump_20


variable (p6 p4 p2 p7 p3 p5 : Prop)
theorem file55_33299 : ((((((p5 ∨ p6) ∧ (True → False)) → ((True ∧ p3) → (p4 ∨ p2))) ∨ (((True → p2) → False) ∨ ((True ∨ True) → False))) ∧ ((((p7 → p7) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_62 : (((p7 → p7) → False) → False) := by
        intro assump_11
        have assump_63 : (p7 → p7) := by
          intro assump_15
          exact assump_15
        let assump_14 := assump_11 assump_63
        apply False.elim assump_14
      let assump_10 := assump_3 assump_62
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_24 =>
        have assump_64 : (((p7 → p7) → False) → False) := by
          intro assump_31
          have assump_65 : (p7 → p7) := by
            intro assump_35
            exact assump_35
          let assump_34 := assump_31 assump_65
          apply False.elim assump_34
        let assump_30 := assump_3 assump_64
        apply False.elim assump_30
      case inr assump_25 =>
        have assump_66 : (((p7 → p7) → False) → False) := by
          intro assump_49
          have assump_67 : (p7 → p7) := by
            intro assump_53
            exact assump_53
          let assump_52 := assump_49 assump_67
          apply False.elim assump_52
        let assump_48 := assump_3 assump_66
        apply False.elim assump_48


variable (p5 p2 p1 p6 p0 p4 p3 : Prop)
theorem file55_34778 : (((((p2 ∨ p1) → (p6 → p0)) → False) ∧ (((p0 ∨ True) → (p5 ∧ p2)) ∧ ((p6 → False) ∨ (p5 → p1)))) → ((((p6 ∨ False) ∧ (p4 ∧ p0)) → ((p3 → p6) ∨ (True ∧ p6))) ∨ (((p6 ∨ p6) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_16
            case intro assump_21 assump_22 =>
              apply Or.inl
              intro assump_27
              exact assump_17
          case inr assump_18 =>
            apply False.elim assump_18
      case inr assump_11 =>
        apply Or.inl
        intro assump_34
        cases assump_34
        case intro assump_35 assump_36 =>
          cases assump_35
          case inl assump_37 =>
            cases assump_36
            case intro assump_41 assump_42 =>
              apply Or.inl
              intro assump_47
              exact assump_37
          case inr assump_38 =>
            apply False.elim assump_38


variable (p5 p4 p6 : Prop)
theorem file55_36027 : ((((((True ∨ p5) ∨ (p6 ∧ p4)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p5) ∨ (p6 ∧ p4)) → False) → False) := by
    intro assump_5
    have assump_16 : ((True ∨ p5) ∨ (p6 ∧ p4)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p4 p5 p1 : Prop)
theorem file55_36508 : ((((((False → p4) ∨ (p5 ∨ p3)) ∧ ((p1 → False) ∧ (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_51 : ((((False → p4) ∨ (p5 ∨ p3)) ∧ ((p1 → False) ∧ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_52 : True := by
            apply True.intro
          let assump_18 := assump_13 assump_52
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case inl assump_22 =>
          cases assump_7
          case intro assump_26 assump_27 =>
            have assump_53 : True := by
              apply True.intro
            let assump_32 := assump_27 assump_53
            apply False.elim assump_32
        case inr assump_23 =>
          cases assump_7
          case intro assump_38 assump_39 =>
            have assump_54 : True := by
              apply True.intro
            let assump_44 := assump_39 assump_54
            apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p3 p2 p5 p1 p6 p4 p0 : Prop)
theorem file55_37754 : ((((((p3 → p4) → (p3 ∨ p6)) ∧ ((p3 ∨ p1) → False)) → (((p6 → p5) ∨ (p2 → False)) → ((False → p2) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p3 → p4) → (p3 ∨ p6)) ∧ ((p3 ∨ p1) → False)) → (((p6 → p5) ∨ (p2 → False)) → ((False → p2) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
    case inr assump_8 =>
      cases assump_5
      case intro assump_22 assump_23 =>
        apply Or.inl
        intro assump_28
        apply False.elim assump_28
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p5 p4 p7 p6 p0 p3 p1 p2 : Prop)
theorem file55_38568 : (((((True ∧ True) → False) → ((False ∧ p3) ∨ (p6 → p7))) ∨ (((p2 ∧ False) → (p3 ∨ p2)) → ((p0 → False) ∧ (p4 ∨ p6)))) → ((((p6 ∧ p6) ∧ (p5 ∧ p1)) → ((p1 ∨ p1) ∨ (p3 ∨ p5))) ∨ (((p2 ∧ p6) → (True → False)) ∧ ((p5 ∧ p1) ∧ (True → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply Or.inl
          exact assump_16
  case inr assump_3 =>
    apply Or.inl
    intro assump_23
    cases assump_23
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_25
        case intro assump_32 assump_33 =>
          apply Or.inl
          apply Or.inl
          exact assump_33


variable (p2 p0 p6 p3 p5 p4 p7 p1 : Prop)
theorem file55_39542 : (((((p3 ∧ p5) ∧ (p1 → False)) → ((p7 → False) ∨ (p7 → False))) ∨ (((p6 → False) → False) ∧ ((p2 ∨ False) → False))) → ((((p3 ∧ p2) → (p1 ∧ p3)) ∧ ((True ∧ p1) → False)) → (((p7 → True) ∨ (p4 ∧ p4)) ∨ ((False ∧ p1) ∨ (p0 → p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      apply Or.inl
      apply Or.inl
      intro assump_13
      apply True.intro
    case inr assump_10 =>
      cases assump_10
      case intro assump_14 assump_15 =>
        apply Or.inl
        apply Or.inl
        intro assump_20
        apply True.intro


variable (p3 p7 p6 p4 p1 p5 p2 : Prop)
theorem file55_40232 : (((((p6 ∨ p2) ∧ (p2 ∧ True)) ∨ ((p3 → False) → (False → p4))) → False) → ((((False ∧ p7) → (p3 → False)) ∧ ((p1 → p5) → False)) ∨ (((True ∧ p2) → False) ∨ ((p6 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8
  intro assump_12
  have assump_24 : (((p6 ∨ p2) ∧ (p2 ∧ True)) ∨ ((p3 → False) → (False → p4))) := by
    apply Or.inr
    intro assump_17
    intro assump_18
    apply False.elim assump_18
  let assump_16 := assump_1 assump_24
  apply False.elim assump_16


variable (p3 p5 p7 p4 p2 : Prop)
theorem file55_40899 : (((((p4 → p7) ∨ (p3 ∨ p2)) → ((p4 ∧ p5) ∨ (p7 ∨ True))) → False) → False) := by
  intro assump_28
  have assump_46 : (((p4 → p7) ∨ (p3 ∨ p2)) → ((p4 ∧ p5) ∨ (p7 ∨ True))) := by
    intro assump_32
    cases assump_32
    case inl assump_33 =>
      apply Or.inr
      apply Or.inr
      apply True.intro
    case inr assump_34 =>
      cases assump_34
      case inl assump_37 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
      case inr assump_38 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
  let assump_31 := assump_28 assump_46
  apply False.elim assump_31


variable (p7 p2 p3 p0 p5 : Prop)
theorem file55_41566 : ((((((p3 ∨ False) ∧ (p7 → p0)) → ((p7 → p7) ∨ (p7 → False))) → (((False ∧ p5) → False) ∨ ((p7 ∨ p5) ∧ (True ∧ p2)))) → False) → False) := by
  intro assump_12
  have assump_27 : ((((p3 ∨ False) ∧ (p7 → p0)) → ((p7 → p7) ∨ (p7 → False))) → (((False ∧ p5) → False) ∨ ((p7 ∨ p5) ∧ (True ∧ p2)))) := by
    intro assump_16
    apply Or.inl
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      apply False.elim assump_20
  let assump_15 := assump_12 assump_27
  apply False.elim assump_15


variable (p1 p2 p3 p7 p6 p0 : Prop)
theorem file55_42141 : (((((p7 ∨ p6) → (False ∧ p3)) → ((p7 → p7) ∧ (False → p6))) → False) → ((((p7 → False) → (p7 ∧ False)) ∧ ((False ∨ p1) ∨ (True ∨ p0))) ∨ (((p2 ∧ p2) ∨ (p1 ∧ p3)) ∨ ((p2 ∨ p6) → (False → False))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  apply And.intro
  have assump_37 : (((p7 ∨ p6) → (False ∧ p3)) → ((p7 → p7) ∧ (False → p6))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    exact assump_10
    intro assump_15
    apply False.elim assump_15
  let assump_8 := assump_1 assump_37
  apply False.elim assump_8
  have assump_38 : (((p7 ∨ p6) → (False ∧ p3)) → ((p7 → p7) ∧ (False → p6))) := by
    intro assump_25
    apply And.intro
    intro assump_26
    exact assump_26
    intro assump_31
    apply False.elim assump_31
  let assump_24 := assump_1 assump_38
  apply False.elim assump_24
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p7 p2 p0 p4 p6 p5 p3 : Prop)
theorem file55_43100 : (((((True ∧ False) → False) ∨ ((p7 ∧ p2) → False)) → (((False → False) ∨ (p7 ∧ p7)) ∨ ((p0 → False) → (True → False)))) ∨ ((((p3 ∧ p6) → False) → ((True ∨ p4) ∨ (p6 → False))) ∨ (((p2 ∧ p0) → (p5 → False)) ∧ ((p5 → p7) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply False.elim assump_11


variable (p7 : Prop)
theorem file55_43645 : (((((p7 ∨ False) ∧ (False → False)) → ((False → False) ∨ (False → False))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p7 ∨ False) ∧ (False → False)) → ((False → False) ∨ (False → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      case inr assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p1 p2 p5 p0 p7 p4 : Prop)
theorem file55_44247 : (((((p7 → p2) ∨ (True → False)) ∧ ((p5 ∧ False) → (False ∨ p5))) → False) → ((((p0 → p1) → False) → ((False ∧ True) → False)) → (((False → False) ∨ (False → False)) → ((p4 ∨ True) ∨ (p0 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_5 =>
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p0 p1 p4 p7 p6 p5 : Prop)
theorem file55_44733 : (((((False ∧ True) → False) ∨ ((True ∧ p6) → (False → False))) ∧ (((False → p7) ∨ (p1 → p0)) → False)) → ((((p5 → False) → False) ∧ ((p7 ∨ p1) → False)) ∧ (((p4 → p0) ∨ (p5 ∧ False)) → ((p0 → False) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_130 : ((False → p7) ∨ (p1 → p0)) := by
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_6 assump_130
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_131 : ((False → p7) ∨ (p1 → p0)) := by
        apply Or.inl
        intro assump_25
        apply False.elim assump_25
      let assump_24 := assump_6 assump_131
      apply False.elim assump_24
  intro assump_31
  cases assump_31
  case inl assump_32 =>
    cases assump_1
    case intro assump_36 assump_37 =>
      cases assump_36
      case inl assump_38 =>
        have assump_132 : ((False → p7) ∨ (p1 → p0)) := by
          apply Or.inl
          intro assump_45
          apply False.elim assump_45
        let assump_44 := assump_37 assump_132
        apply False.elim assump_44
      case inr assump_39 =>
        have assump_133 : ((False → p7) ∨ (p1 → p0)) := by
          apply Or.inl
          intro assump_56
          apply False.elim assump_56
        let assump_55 := assump_37 assump_133
        apply False.elim assump_55
  case inr assump_33 =>
    cases assump_1
    case intro assump_64 assump_65 =>
      cases assump_64
      case inl assump_66 =>
        have assump_134 : ((False → p7) ∨ (p1 → p0)) := by
          apply Or.inl
          intro assump_73
          apply False.elim assump_73
        let assump_72 := assump_65 assump_134
        apply False.elim assump_72
      case inr assump_67 =>
        have assump_135 : ((False → p7) ∨ (p1 → p0)) := by
          apply Or.inl
          intro assump_84
          apply False.elim assump_84
        let assump_83 := assump_65 assump_135
        apply False.elim assump_83
  intro assump_90
  intro assump_91
  cases assump_90
  case inl assump_94 =>
    cases assump_1
    case intro assump_98 assump_99 =>
      cases assump_98
      case inl assump_100 =>
        have assump_136 : ((False → p7) ∨ (p1 → p0)) := by
          apply Or.inl
          intro assump_107
          apply False.elim assump_107
        let assump_106 := assump_99 assump_136
        apply False.elim assump_106
      case inr assump_101 =>
        have assump_137 : ((False → p7) ∨ (p1 → p0)) := by
          apply Or.inl
          intro assump_118
          apply False.elim assump_118
        let assump_117 := assump_99 assump_137
        apply False.elim assump_117
  case inr assump_95 =>
    cases assump_95
    case intro assump_124 assump_125 =>
      apply False.elim assump_125


variable (p1 p7 p2 p0 : Prop)
theorem file55_47671 : ((((((False → p7) ∨ (p1 ∧ p0)) ∨ ((p7 → p2) → False)) ∨ (((True → False) → False) ∨ ((False ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → p7) ∨ (p1 ∧ p0)) ∨ ((p7 → p2) → False)) ∨ (((True → False) → False) ∨ ((False ∧ p1) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p1 p4 p3 : Prop)
theorem file55_48172 : (((((p1 → p6) → (False → True)) → False) ∧ (((True ∨ p3) → False) ∧ ((p4 ∧ True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : (True ∨ p3) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_6 assump_17
      apply False.elim assump_13


variable (p5 p3 p2 p4 p7 p6 p0 : Prop)
theorem file55_48627 : ((((((p6 ∨ p3) ∧ (p2 ∨ p7)) ∨ ((p7 ∧ False) → (True ∨ True))) → False) ∧ ((((p5 ∧ False) ∧ (p0 → p5)) → ((p2 ∧ p0) → False)) ∨ (((True ∧ p6) ∧ (p4 ∨ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_36 : (((p6 ∨ p3) ∧ (p2 ∨ p7)) ∨ ((p7 ∧ False) → (True ∨ True))) := by
        apply Or.inr
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      let assump_11 := assump_2 assump_36
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_37 : (((p6 ∨ p3) ∧ (p2 ∨ p7)) ∨ ((p7 ∧ False) → (True ∨ True))) := by
        apply Or.inr
        intro assump_26
        cases assump_26
        case intro assump_27 assump_28 =>
          apply False.elim assump_28
      let assump_25 := assump_2 assump_37
      apply False.elim assump_25


variable (p5 p0 p4 p6 p2 p1 p3 p7 : Prop)
theorem file55_49632 : (((((p4 ∧ True) ∨ (p5 ∧ p0)) → False) → (((p5 → False) → (p5 → False)) ∨ ((True → False) ∧ (p1 ∧ p2)))) ∨ ((((p1 ∨ p7) ∨ (p1 ∨ p0)) ∨ ((p4 ∨ p6) → (False → False))) → (((p4 → p4) → False) → ((True ∨ p3) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_14 : p5 := by
    exact assump_5
  let assump_10 := assump_4 assump_14
  apply False.elim assump_10


variable (p3 p0 p6 p2 p1 : Prop)
theorem file55_50112 : ((((((False → False) → False) → False) ∨ (((p0 ∧ p3) → False) ∧ ((p6 ∧ p1) ∨ (p6 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p0 ∧ p3) → False) ∧ ((p6 ∧ p1) ∨ (p6 ∧ p2)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p3 p0 p2 p5 p7 p1 : Prop)
theorem file55_50685 : ((((((p7 → p0) ∧ (True ∨ p3)) ∧ ((p3 ∨ p0) → (p3 → p1))) ∨ (((p3 → p1) ∨ (p5 → p3)) ∨ ((True ∧ p0) ∧ (p6 → False)))) ∧ ((((True → False) → False) ∨ ((p2 ∧ p7) ∧ (True → p6))) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_19
          case inl assump_22 =>
            have assump_115 : (((True → False) → False) ∨ ((p2 ∧ p7) ∧ (True → p6))) := by
              apply Or.inl
              intro assump_31
              have assump_116 : True := by
                apply True.intro
              let assump_34 := assump_31 assump_116
              apply False.elim assump_34
            let assump_30 := assump_13 assump_115
            apply False.elim assump_30
          case inr assump_23 =>
            have assump_117 : (((True → False) → False) ∨ ((p2 ∧ p7) ∧ (True → p6))) := by
              apply Or.inl
              intro assump_48
              have assump_118 : True := by
                apply True.intro
              let assump_51 := assump_48 assump_118
              apply False.elim assump_51
            let assump_47 := assump_13 assump_117
            apply False.elim assump_47
    case inr assump_15 =>
      cases assump_15
      case inl assump_58 =>
        cases assump_58
        case inl assump_60 =>
          have assump_119 : (((True → False) → False) ∨ ((p2 ∧ p7) ∧ (True → p6))) := by
            apply Or.inl
            intro assump_67
            have assump_120 : True := by
              apply True.intro
            let assump_70 := assump_67 assump_120
            apply False.elim assump_70
          let assump_66 := assump_13 assump_119
          apply False.elim assump_66
        case inr assump_61 =>
          have assump_121 : (((True → False) → False) ∨ ((p2 ∧ p7) ∧ (True → p6))) := by
            apply Or.inl
            intro assump_82
            have assump_122 : True := by
              apply True.intro
            let assump_85 := assump_82 assump_122
            apply False.elim assump_85
          let assump_81 := assump_13 assump_121
          apply False.elim assump_81
      case inr assump_59 =>
        cases assump_59
        case intro assump_92 assump_93 =>
          cases assump_92
          case intro assump_94 assump_95 =>
            have assump_123 : (((True → False) → False) ∨ ((p2 ∧ p7) ∧ (True → p6))) := by
              apply Or.inl
              intro assump_105
              have assump_124 : True := by
                apply True.intro
              let assump_108 := assump_105 assump_124
              apply False.elim assump_108
            let assump_104 := assump_13 assump_123
            apply False.elim assump_104


variable (p6 p5 p4 p3 p7 : Prop)
theorem file55_53602 : (((((p5 ∧ p4) ∨ (False ∨ p4)) → ((p7 ∧ p5) → (False → False))) → False) → ((((p3 ∨ p6) → (False → False)) ∨ ((True → p4) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_31 : (((p5 ∧ p4) ∨ (False ∨ p4)) → ((p7 ∧ p5) → (False → False))) := by
      intro assump_10
      intro assump_11
      intro assump_12
      apply False.elim assump_12
    let assump_9 := assump_1 assump_31
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_32 : (((p5 ∧ p4) ∨ (False ∨ p4)) → ((p7 ∧ p5) → (False → False))) := by
      intro assump_23
      intro assump_24
      intro assump_25
      apply False.elim assump_25
    let assump_22 := assump_1 assump_32
    apply False.elim assump_22


variable (p0 p7 p2 p4 p1 p5 p3 p6 : Prop)
theorem file55_54426 : ((((((p1 → p7) → (p4 ∨ p2)) → False) ∧ (((p5 ∧ p7) ∧ (True → False)) ∧ ((True ∨ p5) ∨ (False ∨ p3)))) ∧ ((((p0 ∨ True) ∨ (False ∨ p5)) ∨ ((True → p5) ∧ (p7 → p6))) ∨ (((p1 ∧ p0) ∧ (p1 ∨ p4)) ∨ ((p4 ∧ p0) ∨ (p0 ∨ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_9
            case inl assump_20 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_3
                case inl assump_26 =>
                  cases assump_26
                  case inl assump_28 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_30
                      case inl assump_32 =>
                        have assump_370 : True := by
                          apply True.intro
                        let assump_37 := assump_11 assump_370
                        apply False.elim assump_37
                      case inr assump_33 =>
                        have assump_371 : True := by
                          apply True.intro
                        let assump_43 := assump_11 assump_371
                        apply False.elim assump_43
                    case inr assump_31 =>
                      cases assump_31
                      case inl assump_47 =>
                        apply False.elim assump_47
                      case inr assump_48 =>
                        have assump_372 : True := by
                          apply True.intro
                        let assump_54 := assump_11 assump_372
                        apply False.elim assump_54
                  case inr assump_29 =>
                    cases assump_29
                    case intro assump_58 assump_59 =>
                      have assump_373 : True := by
                        apply True.intro
                      let assump_68 := assump_11 assump_373
                      apply False.elim assump_68
                case inr assump_27 =>
                  cases assump_27
                  case inl assump_72 =>
                    cases assump_72
                    case intro assump_74 assump_75 =>
                      cases assump_74
                      case intro assump_76 assump_77 =>
                        cases assump_75
                        case inl assump_82 =>
                          have assump_374 : True := by
                            apply True.intro
                          let assump_89 := assump_11 assump_374
                          apply False.elim assump_89
                        case inr assump_83 =>
                          have assump_375 : True := by
                            apply True.intro
                          let assump_98 := assump_11 assump_375
                          apply False.elim assump_98
                  case inr assump_73 =>
                    cases assump_73
                    case inl assump_102 =>
                      cases assump_102
                      case intro assump_104 assump_105 =>
                        have assump_376 : True := by
                          apply True.intro
                        let assump_112 := assump_11 assump_376
                        apply False.elim assump_112
                    case inr assump_103 =>
                      cases assump_103
                      case inl assump_116 =>
                        have assump_377 : True := by
                          apply True.intro
                        let assump_121 := assump_11 assump_377
                        apply False.elim assump_121
                      case inr assump_117 =>
                        have assump_378 : True := by
                          apply True.intro
                        let assump_128 := assump_11 assump_378
                        apply False.elim assump_128
              case inr assump_23 =>
                cases assump_3
                case inl assump_134 =>
                  cases assump_134
                  case inl assump_136 =>
                    cases assump_136
                    case inl assump_138 =>
                      cases assump_138
                      case inl assump_140 =>
                        have assump_379 : True := by
                          apply True.intro
                        let assump_146 := assump_11 assump_379
                        apply False.elim assump_146
                      case inr assump_141 =>
                        have assump_380 : True := by
                          apply True.intro
                        let assump_153 := assump_11 assump_380
                        apply False.elim assump_153
                    case inr assump_139 =>
                      cases assump_139
                      case inl assump_157 =>
                        apply False.elim assump_157
                      case inr assump_158 =>
                        have assump_381 : True := by
                          apply True.intro
                        let assump_165 := assump_11 assump_381
                        apply False.elim assump_165
                  case inr assump_137 =>
                    cases assump_137
                    case intro assump_169 assump_170 =>
                      have assump_382 : True := by
                        apply True.intro
                      let assump_180 := assump_11 assump_382
                      apply False.elim assump_180
                case inr assump_135 =>
                  cases assump_135
                  case inl assump_184 =>
                    cases assump_184
                    case intro assump_186 assump_187 =>
                      cases assump_186
                      case intro assump_188 assump_189 =>
                        cases assump_187
                        case inl assump_194 =>
                          have assump_383 : True := by
                            apply True.intro
                          let assump_202 := assump_11 assump_383
                          apply False.elim assump_202
                        case inr assump_195 =>
                          have assump_384 : True := by
                            apply True.intro
                          let assump_212 := assump_11 assump_384
                          apply False.elim assump_212
                  case inr assump_185 =>
                    cases assump_185
                    case inl assump_216 =>
                      cases assump_216
                      case intro assump_218 assump_219 =>
                        have assump_385 : True := by
                          apply True.intro
                        let assump_227 := assump_11 assump_385
                        apply False.elim assump_227
                    case inr assump_217 =>
                      cases assump_217
                      case inl assump_231 =>
                        have assump_386 : True := by
                          apply True.intro
                        let assump_237 := assump_11 assump_386
                        apply False.elim assump_237
                      case inr assump_232 =>
                        have assump_387 : True := by
                          apply True.intro
                        let assump_245 := assump_11 assump_387
                        apply False.elim assump_245
            case inr assump_21 =>
              cases assump_21
              case inl assump_249 =>
                apply False.elim assump_249
              case inr assump_250 =>
                cases assump_3
                case inl assump_255 =>
                  cases assump_255
                  case inl assump_257 =>
                    cases assump_257
                    case inl assump_259 =>
                      cases assump_259
                      case inl assump_261 =>
                        have assump_388 : True := by
                          apply True.intro
                        let assump_267 := assump_11 assump_388
                        apply False.elim assump_267
                      case inr assump_262 =>
                        have assump_389 : True := by
                          apply True.intro
                        let assump_274 := assump_11 assump_389
                        apply False.elim assump_274
                    case inr assump_260 =>
                      cases assump_260
                      case inl assump_278 =>
                        apply False.elim assump_278
                      case inr assump_279 =>
                        have assump_390 : True := by
                          apply True.intro
                        let assump_286 := assump_11 assump_390
                        apply False.elim assump_286
                  case inr assump_258 =>
                    cases assump_258
                    case intro assump_290 assump_291 =>
                      have assump_391 : True := by
                        apply True.intro
                      let assump_301 := assump_11 assump_391
                      apply False.elim assump_301
                case inr assump_256 =>
                  cases assump_256
                  case inl assump_305 =>
                    cases assump_305
                    case intro assump_307 assump_308 =>
                      cases assump_307
                      case intro assump_309 assump_310 =>
                        cases assump_308
                        case inl assump_315 =>
                          have assump_392 : True := by
                            apply True.intro
                          let assump_323 := assump_11 assump_392
                          apply False.elim assump_323
                        case inr assump_316 =>
                          have assump_393 : True := by
                            apply True.intro
                          let assump_333 := assump_11 assump_393
                          apply False.elim assump_333
                  case inr assump_306 =>
                    cases assump_306
                    case inl assump_337 =>
                      cases assump_337
                      case intro assump_339 assump_340 =>
                        have assump_394 : True := by
                          apply True.intro
                        let assump_348 := assump_11 assump_394
                        apply False.elim assump_348
                    case inr assump_338 =>
                      cases assump_338
                      case inl assump_352 =>
                        have assump_395 : True := by
                          apply True.intro
                        let assump_358 := assump_11 assump_395
                        apply False.elim assump_358
                      case inr assump_353 =>
                        have assump_396 : True := by
                          apply True.intro
                        let assump_366 := assump_11 assump_396
                        apply False.elim assump_366


variable (p6 p5 p4 p0 : Prop)
theorem file55_65684 : (((((p4 ∨ p0) ∨ (True ∨ True)) ∧ ((p0 → p6) → (False → p4))) → False) → ((((p4 ∧ p5) ∧ (p4 → False)) ∧ ((False ∧ p5) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        have assump_27 : (((p4 ∨ p0) ∨ (True ∨ True)) ∧ ((p0 → p6) → (False → p4))) := by
          apply And.intro
          apply Or.inl
          apply Or.inl
          exact assump_7
          intro assump_20
          intro assump_21
          apply False.elim assump_21
        let assump_19 := assump_1 assump_27
        apply False.elim assump_19


variable (p0 p5 p4 p6 : Prop)
theorem file55_66435 : ((((((p5 → p6) ∧ (p4 ∨ p0)) ∧ ((False ∧ p4) → False)) → False) ∧ ((((False → False) → (False ∧ p5)) → ((p4 → True) ∨ (p0 → False))) → False)) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    have assump_25 : (((False → False) → (False ∧ p5)) → ((p4 → True) ∨ (p0 → False))) := by
      intro assump_18
      apply Or.inl
      intro assump_21
      apply True.intro
    let assump_17 := assump_12 assump_25
    apply False.elim assump_17


variable (p7 p4 p3 p1 p5 p2 : Prop)
theorem file55_66975 : ((((((p2 ∨ p7) → False) → False) → False) ∧ ((((p5 → False) → (False → p4)) ∨ ((p3 ∧ p1) → False)) ∧ (((p5 ∨ p4) ∨ (p5 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_42 : ((p5 ∨ p4) ∨ (p5 → False)) := by
          apply Or.inr
          intro assump_15
          have assump_43 : ((p5 ∨ p4) ∨ (p5 → False)) := by
            apply Or.inl
            apply Or.inl
            exact assump_15
          let assump_19 := assump_7 assump_43
          apply False.elim assump_19
        let assump_14 := assump_7 assump_42
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_44 : ((p5 ∨ p4) ∨ (p5 → False)) := by
          apply Or.inr
          intro assump_31
          have assump_45 : ((p5 ∨ p4) ∨ (p5 → False)) := by
            apply Or.inl
            apply Or.inl
            exact assump_31
          let assump_35 := assump_7 assump_45
          apply False.elim assump_35
        let assump_30 := assump_7 assump_44
        apply False.elim assump_30


variable (p5 p3 p4 p7 p2 p0 p6 : Prop)
theorem file55_68205 : (((((True ∧ p6) ∨ (p4 → p5)) ∨ ((p0 ∧ p6) → (p3 ∧ p7))) → (((p6 ∨ p4) ∨ (False → False)) ∨ ((p6 → False) ∧ (True ∧ p2)))) ∨ ((((p6 → p6) ∨ (p4 ∨ p4)) ∧ ((p3 → p2) ∧ (p4 → False))) ∧ (((p7 ∧ p7) → False) → ((p3 → p0) ∧ (p7 ∧ p0))))) := by
  apply Or.inl
  intro assump_15
  cases assump_15
  case inl assump_16 =>
    cases assump_16
    case inl assump_18 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_21
    case inr assump_19 =>
      apply Or.inl
      apply Or.inr
      intro assump_28
      apply False.elim assump_28
  case inr assump_17 =>
    apply Or.inl
    apply Or.inr
    intro assump_33
    apply False.elim assump_33


variable (p6 p7 p0 p3 p4 p5 p2 : Prop)
theorem file55_69004 : (((((p4 ∧ p0) → False) → ((False → p7) ∧ (False ∨ True))) ∧ (((p7 ∧ p2) ∨ (p5 ∨ p0)) ∧ ((True → False) ∧ (p0 ∨ p2)))) → ((((p4 ∨ True) ∨ (p6 ∧ p0)) ∨ ((p3 ∨ p4) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case intro assump_11 assump_12 =>
          cases assump_12
          case intro assump_15 assump_16 =>
            cases assump_15
            case inl assump_17 =>
              cases assump_17
              case intro assump_19 assump_20 =>
                cases assump_16
                case intro assump_25 assump_26 =>
                  cases assump_26
                  case inl assump_29 =>
                    have assump_341 : True := by
                      apply True.intro
                    let assump_34 := assump_25 assump_341
                    apply False.elim assump_34
                  case inr assump_30 =>
                    have assump_342 : True := by
                      apply True.intro
                    let assump_41 := assump_25 assump_342
                    apply False.elim assump_41
            case inr assump_18 =>
              cases assump_18
              case inl assump_45 =>
                cases assump_16
                case intro assump_49 assump_50 =>
                  cases assump_50
                  case inl assump_53 =>
                    have assump_343 : True := by
                      apply True.intro
                    let assump_58 := assump_49 assump_343
                    apply False.elim assump_58
                  case inr assump_54 =>
                    have assump_344 : True := by
                      apply True.intro
                    let assump_65 := assump_49 assump_344
                    apply False.elim assump_65
              case inr assump_46 =>
                cases assump_16
                case intro assump_71 assump_72 =>
                  cases assump_72
                  case inl assump_75 =>
                    have assump_345 : True := by
                      apply True.intro
                    let assump_80 := assump_71 assump_345
                    apply False.elim assump_80
                  case inr assump_76 =>
                    have assump_346 : True := by
                      apply True.intro
                    let assump_87 := assump_71 assump_346
                    apply False.elim assump_87
      case inr assump_8 =>
        cases assump_1
        case intro assump_93 assump_94 =>
          cases assump_94
          case intro assump_97 assump_98 =>
            cases assump_97
            case inl assump_99 =>
              cases assump_99
              case intro assump_101 assump_102 =>
                cases assump_98
                case intro assump_107 assump_108 =>
                  cases assump_108
                  case inl assump_111 =>
                    have assump_347 : True := by
                      apply True.intro
                    let assump_116 := assump_107 assump_347
                    apply False.elim assump_116
                  case inr assump_112 =>
                    have assump_348 : True := by
                      apply True.intro
                    let assump_123 := assump_107 assump_348
                    apply False.elim assump_123
            case inr assump_100 =>
              cases assump_100
              case inl assump_127 =>
                cases assump_98
                case intro assump_131 assump_132 =>
                  cases assump_132
                  case inl assump_135 =>
                    have assump_349 : True := by
                      apply True.intro
                    let assump_140 := assump_131 assump_349
                    apply False.elim assump_140
                  case inr assump_136 =>
                    have assump_350 : True := by
                      apply True.intro
                    let assump_147 := assump_131 assump_350
                    apply False.elim assump_147
              case inr assump_128 =>
                cases assump_98
                case intro assump_153 assump_154 =>
                  cases assump_154
                  case inl assump_157 =>
                    have assump_351 : True := by
                      apply True.intro
                    let assump_162 := assump_153 assump_351
                    apply False.elim assump_162
                  case inr assump_158 =>
                    have assump_352 : True := by
                      apply True.intro
                    let assump_169 := assump_153 assump_352
                    apply False.elim assump_169
    case inr assump_6 =>
      cases assump_6
      case intro assump_173 assump_174 =>
        cases assump_1
        case intro assump_179 assump_180 =>
          cases assump_180
          case intro assump_183 assump_184 =>
            cases assump_183
            case inl assump_185 =>
              cases assump_185
              case intro assump_187 assump_188 =>
                cases assump_184
                case intro assump_193 assump_194 =>
                  cases assump_194
                  case inl assump_197 =>
                    have assump_353 : True := by
                      apply True.intro
                    let assump_202 := assump_193 assump_353
                    apply False.elim assump_202
                  case inr assump_198 =>
                    have assump_354 : True := by
                      apply True.intro
                    let assump_209 := assump_193 assump_354
                    apply False.elim assump_209
            case inr assump_186 =>
              cases assump_186
              case inl assump_213 =>
                cases assump_184
                case intro assump_217 assump_218 =>
                  cases assump_218
                  case inl assump_221 =>
                    have assump_355 : True := by
                      apply True.intro
                    let assump_226 := assump_217 assump_355
                    apply False.elim assump_226
                  case inr assump_222 =>
                    have assump_356 : True := by
                      apply True.intro
                    let assump_233 := assump_217 assump_356
                    apply False.elim assump_233
              case inr assump_214 =>
                cases assump_184
                case intro assump_239 assump_240 =>
                  cases assump_240
                  case inl assump_243 =>
                    have assump_357 : True := by
                      apply True.intro
                    let assump_248 := assump_239 assump_357
                    apply False.elim assump_248
                  case inr assump_244 =>
                    have assump_358 : True := by
                      apply True.intro
                    let assump_255 := assump_239 assump_358
                    apply False.elim assump_255
  case inr assump_4 =>
    cases assump_1
    case intro assump_261 assump_262 =>
      cases assump_262
      case intro assump_265 assump_266 =>
        cases assump_265
        case inl assump_267 =>
          cases assump_267
          case intro assump_269 assump_270 =>
            cases assump_266
            case intro assump_275 assump_276 =>
              cases assump_276
              case inl assump_279 =>
                have assump_359 : True := by
                  apply True.intro
                let assump_284 := assump_275 assump_359
                apply False.elim assump_284
              case inr assump_280 =>
                have assump_360 : True := by
                  apply True.intro
                let assump_291 := assump_275 assump_360
                apply False.elim assump_291
        case inr assump_268 =>
          cases assump_268
          case inl assump_295 =>
            cases assump_266
            case intro assump_299 assump_300 =>
              cases assump_300
              case inl assump_303 =>
                have assump_361 : True := by
                  apply True.intro
                let assump_308 := assump_299 assump_361
                apply False.elim assump_308
              case inr assump_304 =>
                have assump_362 : True := by
                  apply True.intro
                let assump_315 := assump_299 assump_362
                apply False.elim assump_315
          case inr assump_296 =>
            cases assump_266
            case intro assump_321 assump_322 =>
              cases assump_322
              case inl assump_325 =>
                have assump_363 : True := by
                  apply True.intro
                let assump_330 := assump_321 assump_363
                apply False.elim assump_330
              case inr assump_326 =>
                have assump_364 : True := by
                  apply True.intro
                let assump_337 := assump_321 assump_364
                apply False.elim assump_337


variable (p2 p1 p4 p6 p3 p5 : Prop)
theorem file55_78118 : ((((((p4 ∧ p2) ∨ (p3 ∨ p3)) ∧ ((p5 ∨ p1) → (p2 ∨ p3))) ∧ (((p2 ∧ p1) → (p4 → p2)) ∨ ((False ∨ p3) → False))) ∧ ((((p5 → False) ∨ (True → False)) ∧ ((False ∨ p1) → (p3 ∧ p6))) ∧ (((p6 ∧ p1) → (False → p3)) ∧ ((p3 → p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_5
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case inl assump_26 =>
                    cases assump_23
                    case intro assump_32 assump_33 =>
                      have assump_286 : (p3 → p3) := by
                        intro assump_39
                        exact assump_39
                      let assump_38 := assump_33 assump_286
                      apply False.elim assump_38
                  case inr assump_27 =>
                    cases assump_23
                    case intro assump_49 assump_50 =>
                      have assump_287 : (p3 → p3) := by
                        intro assump_56
                        exact assump_56
                      let assump_55 := assump_50 assump_287
                      apply False.elim assump_55
            case inr assump_19 =>
              cases assump_3
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  cases assump_66
                  case inl assump_68 =>
                    cases assump_65
                    case intro assump_74 assump_75 =>
                      have assump_288 : (p3 → p3) := by
                        intro assump_81
                        exact assump_81
                      let assump_80 := assump_75 assump_288
                      apply False.elim assump_80
                  case inr assump_69 =>
                    cases assump_65
                    case intro assump_91 assump_92 =>
                      have assump_289 : (p3 → p3) := by
                        intro assump_98
                        exact assump_98
                      let assump_97 := assump_92 assump_289
                      apply False.elim assump_97
        case inr assump_9 =>
          cases assump_9
          case inl assump_104 =>
            cases assump_5
            case inl assump_110 =>
              cases assump_3
              case intro assump_114 assump_115 =>
                cases assump_114
                case intro assump_116 assump_117 =>
                  cases assump_116
                  case inl assump_118 =>
                    cases assump_115
                    case intro assump_124 assump_125 =>
                      have assump_290 : (p3 → p3) := by
                        intro assump_131
                        exact assump_131
                      let assump_130 := assump_125 assump_290
                      apply False.elim assump_130
                  case inr assump_119 =>
                    cases assump_115
                    case intro assump_141 assump_142 =>
                      have assump_291 : (p3 → p3) := by
                        intro assump_148
                        exact assump_148
                      let assump_147 := assump_142 assump_291
                      apply False.elim assump_147
            case inr assump_111 =>
              cases assump_3
              case intro assump_156 assump_157 =>
                cases assump_156
                case intro assump_158 assump_159 =>
                  cases assump_158
                  case inl assump_160 =>
                    cases assump_157
                    case intro assump_166 assump_167 =>
                      have assump_292 : (p3 → p3) := by
                        intro assump_173
                        exact assump_173
                      let assump_172 := assump_167 assump_292
                      apply False.elim assump_172
                  case inr assump_161 =>
                    cases assump_157
                    case intro assump_183 assump_184 =>
                      have assump_293 : (p3 → p3) := by
                        intro assump_190
                        exact assump_190
                      let assump_189 := assump_184 assump_293
                      apply False.elim assump_189
          case inr assump_105 =>
            cases assump_5
            case inl assump_200 =>
              cases assump_3
              case intro assump_204 assump_205 =>
                cases assump_204
                case intro assump_206 assump_207 =>
                  cases assump_206
                  case inl assump_208 =>
                    cases assump_205
                    case intro assump_214 assump_215 =>
                      have assump_294 : (p3 → p3) := by
                        intro assump_221
                        exact assump_221
                      let assump_220 := assump_215 assump_294
                      apply False.elim assump_220
                  case inr assump_209 =>
                    cases assump_205
                    case intro assump_231 assump_232 =>
                      have assump_295 : (p3 → p3) := by
                        intro assump_238
                        exact assump_238
                      let assump_237 := assump_232 assump_295
                      apply False.elim assump_237
            case inr assump_201 =>
              cases assump_3
              case intro assump_246 assump_247 =>
                cases assump_246
                case intro assump_248 assump_249 =>
                  cases assump_248
                  case inl assump_250 =>
                    cases assump_247
                    case intro assump_256 assump_257 =>
                      have assump_296 : (p3 → p3) := by
                        intro assump_263
                        exact assump_263
                      let assump_262 := assump_257 assump_296
                      apply False.elim assump_262
                  case inr assump_251 =>
                    cases assump_247
                    case intro assump_273 assump_274 =>
                      have assump_297 : (p3 → p3) := by
                        intro assump_280
                        exact assump_280
                      let assump_279 := assump_274 assump_297
                      apply False.elim assump_279


variable (p5 p7 p6 p1 p2 p0 p4 p3 : Prop)
theorem file55_84895 : ((((((False → False) ∨ (True → p1)) ∧ ((p3 → p4) ∧ (p2 → True))) ∧ (((p1 → False) ∧ (p0 → False)) → ((p5 ∨ p2) ∨ (p5 → p6)))) ∧ ((((p0 ∨ p4) ∧ (p7 ∧ p6)) → ((p7 → False) → (p5 → p6))) → (((p6 ∨ p6) → (p3 → p6)) → False))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_24
        case inl assump_26 =>
          cases assump_25
          case intro assump_30 assump_31 =>
            have assump_136 : (((p0 ∨ p4) ∧ (p7 ∧ p6)) → ((p7 → False) → (p5 → p6))) := by
              intro assump_41
              intro assump_42
              intro assump_43
              cases assump_41
              case intro assump_48 assump_49 =>
                cases assump_48
                case inl assump_50 =>
                  cases assump_49
                  case intro assump_54 assump_55 =>
                    exact assump_55
                case inr assump_51 =>
                  cases assump_49
                  case intro assump_62 assump_63 =>
                    exact assump_63
            let assump_40 := assump_21 assump_136
            have assump_137 : ((p6 ∨ p6) → (p3 → p6)) := by
              intro assump_69
              intro assump_70
              cases assump_69
              case inl assump_73 =>
                exact assump_73
              case inr assump_74 =>
                exact assump_74
            let assump_68 := assump_40 assump_137
            apply False.elim assump_68
        case inr assump_27 =>
          cases assump_25
          case intro assump_84 assump_85 =>
            have assump_138 : (((p0 ∨ p4) ∧ (p7 ∧ p6)) → ((p7 → False) → (p5 → p6))) := by
              intro assump_95
              intro assump_96
              intro assump_97
              cases assump_95
              case intro assump_102 assump_103 =>
                cases assump_102
                case inl assump_104 =>
                  cases assump_103
                  case intro assump_108 assump_109 =>
                    exact assump_109
                case inr assump_105 =>
                  cases assump_103
                  case intro assump_116 assump_117 =>
                    exact assump_117
            let assump_94 := assump_21 assump_138
            have assump_139 : ((p6 ∨ p6) → (p3 → p6)) := by
              intro assump_123
              intro assump_124
              cases assump_123
              case inl assump_127 =>
                exact assump_127
              case inr assump_128 =>
                exact assump_128
            let assump_122 := assump_94 assump_139
            apply False.elim assump_122


variable (p7 p5 p3 p4 p1 : Prop)
theorem file55_87699 : ((((((False ∧ p7) ∧ (p4 ∧ p3)) ∨ ((p3 ∨ True) → False)) → (((p4 ∨ p1) → (p5 → p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((False ∧ p7) ∧ (p4 ∧ p3)) ∨ ((p3 ∨ True) → False)) → (((p4 ∨ p1) → (p5 → p1)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
    case inr assump_10 =>
      have assump_27 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_19 := assump_10 assump_27
      apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p3 p2 p7 p0 p4 : Prop)
theorem file55_88506 : (((((False → False) ∨ (p7 → False)) ∧ ((p0 ∧ p2) ∧ (p3 → False))) → (((False ∧ p3) → False) → ((p3 → p4) ∧ (False → p2)))) ∨ ((((False → False) → False) ∨ ((p2 ∧ p7) → False)) ∧ (((p0 ∨ p2) ∧ (False → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_47 : p3 := by
            exact assump_3
          let assump_24 := assump_15 assump_47
          apply False.elim assump_24
    case inr assump_11 =>
      cases assump_9
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          have assump_48 : p3 := by
            exact assump_3
          let assump_40 := assump_31 assump_48
          apply False.elim assump_40
  intro assump_44
  apply False.elim assump_44


variable (p5 p6 p3 p0 p2 : Prop)
theorem file55_89590 : (((((p2 → False) → (p0 → True)) → False) ∧ (((p5 → False) ∨ (p3 ∨ False)) ∨ ((p6 → False) ∧ (p3 ∨ p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_58 : ((p2 → False) → (p0 → True)) := by
          intro assump_14
          intro assump_15
          apply True.intro
        let assump_13 := assump_2 assump_58
        apply False.elim assump_13
      case inr assump_9 =>
        cases assump_9
        case inl assump_19 =>
          have assump_59 : ((p2 → False) → (p0 → True)) := by
            intro assump_25
            intro assump_26
            apply True.intro
          let assump_24 := assump_2 assump_59
          apply False.elim assump_24
        case inr assump_20 =>
          apply False.elim assump_20
    case inr assump_7 =>
      cases assump_7
      case intro assump_32 assump_33 =>
        cases assump_33
        case inl assump_36 =>
          have assump_60 : ((p2 → False) → (p0 → True)) := by
            intro assump_43
            intro assump_44
            apply True.intro
          let assump_42 := assump_2 assump_60
          apply False.elim assump_42
        case inr assump_37 =>
          have assump_61 : ((p2 → False) → (p0 → True)) := by
            intro assump_53
            intro assump_54
            apply True.intro
          let assump_52 := assump_2 assump_61
          apply False.elim assump_52


variable (p2 p5 p7 p0 p4 p3 p6 : Prop)
theorem file55_91158 : (((((True → p4) ∨ (p6 → p2)) ∨ ((p3 ∧ False) ∧ (p0 → p5))) → False) → ((((False ∨ p7) ∧ (p2 ∨ True)) ∧ ((True → p2) → (True ∧ False))) → (((p4 → False) ∨ (p3 → p3)) ∨ ((p7 ∧ p7) ∨ (p2 → False))))) := by
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
        cases assump_6
        case inl assump_13 =>
          apply Or.inl
          apply Or.inl
          intro assump_21
          have assump_49 : (((True → p4) ∨ (p6 → p2)) ∨ ((p3 ∧ False) ∧ (p0 → p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_26
            exact assump_21
          let assump_25 := assump_1 assump_49
          apply False.elim assump_25
        case inr assump_14 =>
          apply Or.inl
          apply Or.inl
          intro assump_38
          have assump_50 : (((True → p4) ∨ (p6 → p2)) ∨ ((p3 ∧ False) ∧ (p0 → p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_43
            exact assump_38
          let assump_42 := assump_1 assump_50
          apply False.elim assump_42


variable (p5 p7 p2 p4 p6 p0 p1 : Prop)
theorem file55_92458 : (((((p2 → p2) → False) → ((p7 → p6) → False)) → False) → ((((p4 → False) → (p0 → p5)) → False) → (((p1 ∨ False) → (p1 ∧ False)) ∨ ((p1 ∧ p4) ∧ (p4 ∨ p1))))) := by
  intro assump_29
  intro assump_30
  apply Or.inl
  intro assump_35
  apply And.intro
  cases assump_35
  case inl assump_36 =>
    exact assump_36
  case inr assump_37 =>
    apply False.elim assump_37
  cases assump_35
  case inl assump_42 =>
    have assump_66 : (((p2 → p2) → False) → ((p7 → p6) → False)) := by
      intro assump_48
      intro assump_49
      have assump_67 : (p2 → p2) := by
        intro assump_55
        exact assump_55
      let assump_54 := assump_48 assump_67
      apply False.elim assump_54
    let assump_47 := assump_29 assump_66
    apply False.elim assump_47
  case inr assump_43 =>
    apply False.elim assump_43


variable (p3 p0 p4 p1 p2 : Prop)
theorem file55_93329 : ((((((p4 ∧ p2) ∨ (p0 ∨ p4)) → ((False ∧ p1) → (p3 ∨ p0))) ∧ (((False → False) → False) → False)) → False) → False) := by
  intro assump_6
  have assump_29 : ((((p4 ∧ p2) ∨ (p0 ∨ p4)) → ((False ∧ p1) → (p3 ∨ p0))) ∧ (((False → False) → False) → False)) := by
    apply And.intro
    intro assump_10
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
    intro assump_16
    have assump_30 : (False → False) := by
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_16 assump_30
    apply False.elim assump_19
  let assump_9 := assump_6 assump_29
  apply False.elim assump_9


variable (p2 p7 p5 p0 p1 : Prop)
theorem file55_94050 : ((((((p2 ∨ p7) ∨ (True ∨ p1)) ∧ ((True → False) → (False ∨ p0))) ∨ (((p5 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∨ p7) ∨ (True ∨ p1)) ∧ ((True → False) → (False ∨ p0))) ∨ (((p5 → False) → False) → False)) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply Or.inl
    apply True.intro
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p6 p5 p7 : Prop)
theorem file55_94670 : (((((p1 → True) → False) → False) → False) → ((((p7 → False) → (True ∨ p7)) → ((p6 → False) ∧ (False ∧ p1))) → (((p5 → False) → False) → ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  have assump_25 : (((p1 → True) → False) → False) := by
    intro assump_14
    have assump_26 : (p1 → True) := by
      intro assump_18
      apply True.intro
    let assump_17 := assump_14 assump_26
    apply False.elim assump_17
  let assump_13 := assump_1 assump_25
  apply False.elim assump_13


variable (p5 p7 p3 p2 : Prop)
theorem file55_95261 : ((((((p7 ∧ p5) ∧ (p3 → False)) → ((p7 → False) → (p2 → p7))) ∧ (((p5 → False) ∧ (p5 ∨ p5)) → ((p5 → p3) → False))) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p7 ∧ p5) ∧ (p3 → False)) → ((p7 → False) → (p2 → p7))) ∧ (((p5 → False) ∧ (p5 ∨ p5)) → ((p5 → p3) → False))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        exact assump_14
    intro assump_22
    intro assump_23
    cases assump_22
    case intro assump_26 assump_27 =>
      cases assump_27
      case inl assump_30 =>
        have assump_50 : p5 := by
          exact assump_30
        let assump_35 := assump_26 assump_50
        apply False.elim assump_35
      case inr assump_31 =>
        have assump_51 : p5 := by
          exact assump_31
        let assump_42 := assump_26 assump_51
        apply False.elim assump_42
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p7 p3 p0 p2 p5 : Prop)
theorem file55_96353 : (((((False → False) ∨ (p3 → False)) ∧ ((p7 → False) → (True ∨ True))) ∨ (((p2 → False) ∧ (p3 ∧ p0)) ∨ ((False → False) → False))) ∨ ((((p2 ∧ p7) → (p2 → p3)) ∨ ((p0 ∨ p5) → (p7 ∨ False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  apply False.elim assump_1
  intro assump_4
  apply Or.inl
  apply True.intro


variable (p5 p2 p3 p6 p1 p7 p0 : Prop)
theorem file55_96779 : (((((p5 ∨ True) ∨ (p0 ∨ p0)) ∨ ((p3 ∧ p5) → False)) → False) → ((((False → False) → (p7 → p1)) ∨ ((p7 → p1) → (p2 → False))) ∨ (((p1 ∧ False) → False) ∧ ((p7 → p6) ∨ (p7 ∨ p1))))) := by
  intro assump_5
  apply Or.inl
  apply Or.inl
  intro assump_8
  intro assump_9
  have assump_20 : (((p5 ∨ True) ∨ (p0 ∨ p0)) ∨ ((p3 ∧ p5) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_16 := assump_5 assump_20
  apply False.elim assump_16


variable (p5 p7 p2 p0 p3 p1 : Prop)
theorem file55_97320 : (((((True ∨ p5) ∨ (p2 → False)) ∨ ((True → False) ∧ (p5 ∧ p3))) → (((p0 ∨ p2) ∧ (p3 → False)) ∨ ((True ∨ p7) ∨ (p7 → False)))) ∧ ((((p7 → p7) → False) → False) ∨ (((p5 → False) → (p1 ∨ p3)) → False))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inr
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_7 =>
        apply Or.inr
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      apply Or.inr
      apply Or.inl
      apply Or.inl
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply Or.inr
        apply Or.inl
        apply Or.inl
        apply True.intro
  apply Or.inl
  intro assump_24
  have assump_34 : (p7 → p7) := by
    intro assump_28
    exact assump_28
  let assump_27 := assump_24 assump_34
  apply False.elim assump_27


variable (p4 p6 p7 p0 p5 p3 : Prop)
theorem file55_98468 : ((((((p6 ∧ p5) → (p6 ∨ True)) → False) → (((p5 ∨ p5) ∧ (True → False)) → False)) ∧ ((((True ∧ p0) ∨ (p4 ∨ p7)) → ((p4 ∧ p5) → (p4 → False))) ∧ (((p7 → p3) → False) ∧ ((p4 ∨ False) ∧ (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            have assump_28 : p4 := by
              exact assump_16
            let assump_22 := assump_15 assump_28
            apply False.elim assump_22
          case inr assump_17 =>
            apply False.elim assump_17


variable (p3 p1 p0 p5 p2 p4 p7 : Prop)
theorem file55_99280 : (((((p4 → False) → (False → False)) ∨ ((p3 ∨ p5) → False)) ∨ (((p5 ∧ p0) ∨ (p3 ∧ p2)) ∨ ((True → False) ∧ (False ∨ p1)))) ∨ ((((p5 → True) → False) ∨ ((False → False) → False)) ∧ (((True ∧ p2) → (p7 → False)) → ((True ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p4 p2 p0 p5 p1 p3 p7 : Prop)
theorem file55_99692 : ((((((True → False) → (p5 ∨ p7)) → ((p2 → False) → False)) ∨ (((p0 ∨ False) → (p0 → p1)) ∨ ((p3 ∧ True) → (p4 → p2)))) ∧ ((((p7 ∨ False) → (p5 → False)) ∨ ((p1 → False) → (p7 ∧ p3))) ∧ (((True → False) → (p3 ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_116 : ((True → False) → (p3 ∨ p0)) := by
            intro assump_17
            have assump_117 : True := by
              apply True.intro
            let assump_20 := assump_17 assump_117
            apply False.elim assump_20
          let assump_16 := assump_9 assump_116
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_118 : ((True → False) → (p3 ∨ p0)) := by
            intro assump_32
            have assump_119 : True := by
              apply True.intro
            let assump_35 := assump_32 assump_119
            apply False.elim assump_35
          let assump_31 := assump_9 assump_118
          apply False.elim assump_31
    case inr assump_5 =>
      cases assump_5
      case inl assump_42 =>
        cases assump_3
        case intro assump_46 assump_47 =>
          cases assump_46
          case inl assump_48 =>
            have assump_120 : ((True → False) → (p3 ∨ p0)) := by
              intro assump_55
              have assump_121 : True := by
                apply True.intro
              let assump_58 := assump_55 assump_121
              apply False.elim assump_58
            let assump_54 := assump_47 assump_120
            apply False.elim assump_54
          case inr assump_49 =>
            have assump_122 : ((True → False) → (p3 ∨ p0)) := by
              intro assump_70
              have assump_123 : True := by
                apply True.intro
              let assump_73 := assump_70 assump_123
              apply False.elim assump_73
            let assump_69 := assump_47 assump_122
            apply False.elim assump_69
      case inr assump_43 =>
        cases assump_3
        case intro assump_82 assump_83 =>
          cases assump_82
          case inl assump_84 =>
            have assump_124 : ((True → False) → (p3 ∨ p0)) := by
              intro assump_91
              have assump_125 : True := by
                apply True.intro
              let assump_94 := assump_91 assump_125
              apply False.elim assump_94
            let assump_90 := assump_83 assump_124
            apply False.elim assump_90
          case inr assump_85 =>
            have assump_126 : ((True → False) → (p3 ∨ p0)) := by
              intro assump_106
              have assump_127 : True := by
                apply True.intro
              let assump_109 := assump_106 assump_127
              apply False.elim assump_109
            let assump_105 := assump_83 assump_126
            apply False.elim assump_105


variable (p5 p1 p6 p3 p0 p4 : Prop)
theorem file55_102749 : ((((((p4 ∨ True) → (p6 → False)) → ((p4 ∧ p0) ∨ (True ∨ True))) ∨ (((p3 → p1) ∧ (p3 ∧ p5)) → False)) → False) → False) := by
  intro assump_11
  have assump_21 : ((((p4 ∨ True) → (p6 → False)) → ((p4 ∧ p0) ∨ (True ∨ True))) ∨ (((p3 → p1) ∧ (p3 ∧ p5)) → False)) := by
    apply Or.inl
    intro assump_15
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_14 := assump_11 assump_21
  apply False.elim assump_14


variable (p0 p2 p6 p5 p1 : Prop)
theorem file55_103233 : (((((p0 → False) → (p0 → False)) ∧ ((True → False) ∨ (True → False))) → False) ∧ ((((True → True) → (True → False)) → False) ∨ (((p2 ∨ p6) → (p0 ∨ p5)) → ((False → p1) ∨ (False → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_29 : True := by
        apply True.intro
      let assump_10 := assump_6 assump_29
      apply False.elim assump_10
    case inr assump_7 =>
      have assump_30 : True := by
        apply True.intro
      let assump_16 := assump_7 assump_30
      apply False.elim assump_16
  apply Or.inl
  intro assump_20
  have assump_31 : (True → True) := by
    intro assump_24
    apply True.intro
  let assump_23 := assump_20 assump_31
  have assump_32 : True := by
    apply True.intro
  let assump_25 := assump_23 assump_32
  apply False.elim assump_25


variable (p7 p5 p2 p4 p1 p6 p3 : Prop)
theorem file55_104186 : (((((True → False) → False) ∨ ((p3 ∧ False) ∨ (p6 ∧ False))) → False) → ((((p6 → p4) → False) ∨ ((p6 ∨ p1) ∧ (True → False))) ∨ (((p7 ∧ p5) → (p2 → False)) → ((True ∧ p7) ∨ (p4 ∧ p5))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_19 : (((True → False) → False) ∨ ((p3 ∧ False) ∨ (p6 ∧ False))) := by
    apply Or.inl
    intro assump_9
    have assump_20 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p4 p0 p5 : Prop)
theorem file55_104805 : ((((((True → False) ∧ (p0 → p5)) ∨ ((p4 → True) → (True → False))) → (((False ∨ p5) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_33 : ((((True → False) ∧ (p0 → p5)) ∨ ((p4 → True) → (True → False))) → (((False ∨ p5) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_34 : True := by
          apply True.intro
        let assump_18 := assump_11 assump_34
        apply False.elim assump_18
    case inr assump_10 =>
      have assump_35 : (p4 → True) := by
        intro assump_25
        apply True.intro
      let assump_24 := assump_10 assump_35
      have assump_36 : True := by
        apply True.intro
      let assump_26 := assump_24 assump_36
      apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p2 p7 p5 p0 p4 p6 p3 p1 : Prop)
theorem file55_105786 : ((((((False ∧ p4) ∨ (p5 ∧ False)) ∨ ((p3 → False) ∧ (True → False))) ∧ (((p6 ∧ p0) ∨ (p4 ∨ p5)) → ((p5 → p5) ∧ (p6 → False)))) ∧ ((((p2 ∨ p2) ∧ (True ∨ p5)) → ((p5 ∧ p6) → False)) ∨ (((p0 ∨ p6) ∧ (p7 → False)) ∨ ((False ∨ p7) ∨ (p1 ∨ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            apply False.elim assump_10
        case inr assump_9 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
      case inr assump_7 =>
        cases assump_7
        case intro assump_20 assump_21 =>
          cases assump_3
          case inl assump_28 =>
            have assump_102 : True := by
              apply True.intro
            let assump_34 := assump_21 assump_102
            apply False.elim assump_34
          case inr assump_29 =>
            cases assump_29
            case inl assump_38 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                cases assump_40
                case inl assump_42 =>
                  have assump_103 : True := by
                    apply True.intro
                  let assump_51 := assump_21 assump_103
                  apply False.elim assump_51
                case inr assump_43 =>
                  have assump_104 : True := by
                    apply True.intro
                  let assump_62 := assump_21 assump_104
                  apply False.elim assump_62
            case inr assump_39 =>
              cases assump_39
              case inl assump_66 =>
                cases assump_66
                case inl assump_68 =>
                  apply False.elim assump_68
                case inr assump_69 =>
                  have assump_105 : True := by
                    apply True.intro
                  let assump_76 := assump_21 assump_105
                  apply False.elim assump_76
              case inr assump_67 =>
                cases assump_67
                case inl assump_80 =>
                  have assump_106 : True := by
                    apply True.intro
                  let assump_86 := assump_21 assump_106
                  apply False.elim assump_86
                case inr assump_81 =>
                  have assump_107 : True := by
                    apply True.intro
                  let assump_98 := assump_21 assump_107
                  apply False.elim assump_98


variable (p5 p0 p2 p7 p1 p4 p6 p3 : Prop)
theorem file55_108489 : (((((p6 ∧ p3) → False) ∧ ((p6 → p2) ∧ (p4 ∧ False))) ∧ (((p0 ∨ True) ∧ (False → p2)) ∧ ((False → False) → False))) → ((((p0 ∨ p6) ∧ (p1 → False)) ∨ ((p7 → False) ∨ (p6 ∨ p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_16
            case intro assump_19 assump_20 =>
              cases assump_20
              case intro assump_23 assump_24 =>
                apply False.elim assump_24
      case inr assump_8 =>
        cases assump_1
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            cases assump_36
            case intro assump_39 assump_40 =>
              cases assump_40
              case intro assump_43 assump_44 =>
                apply False.elim assump_44
  case inr assump_4 =>
    cases assump_4
    case inl assump_49 =>
      cases assump_1
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          cases assump_56
          case intro assump_59 assump_60 =>
            cases assump_60
            case intro assump_63 assump_64 =>
              apply False.elim assump_64
    case inr assump_50 =>
      cases assump_50
      case inl assump_69 =>
        cases assump_1
        case intro assump_73 assump_74 =>
          cases assump_73
          case intro assump_75 assump_76 =>
            cases assump_76
            case intro assump_79 assump_80 =>
              cases assump_80
              case intro assump_83 assump_84 =>
                apply False.elim assump_84
      case inr assump_70 =>
        cases assump_1
        case intro assump_91 assump_92 =>
          cases assump_91
          case intro assump_93 assump_94 =>
            cases assump_94
            case intro assump_97 assump_98 =>
              cases assump_98
              case intro assump_101 assump_102 =>
                apply False.elim assump_102


variable (p0 p6 p4 p2 p3 p1 p7 : Prop)
theorem file55_110755 : (((((p4 ∧ p4) ∨ (p0 → True)) → False) ∧ (((p6 ∨ p3) ∧ (p1 ∨ False)) ∧ ((p4 ∧ p7) ∨ (p2 ∧ p2)))) → ((((True → False) → False) → False) → False)) := by
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
            case inl assump_21 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                have assump_93 : ((p4 ∧ p4) ∨ (p0 → True)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_23
                  exact assump_23
                let assump_33 := assump_5 assump_93
                apply False.elim assump_33
            case inr assump_22 =>
              cases assump_22
              case intro assump_37 assump_38 =>
                have assump_94 : ((p4 ∧ p4) ∨ (p0 → True)) := by
                  apply Or.inr
                  intro assump_48
                  apply True.intro
                let assump_47 := assump_5 assump_94
                apply False.elim assump_47
          case inr assump_18 =>
            apply False.elim assump_18
        case inr assump_14 =>
          cases assump_12
          case inl assump_56 =>
            cases assump_10
            case inl assump_60 =>
              cases assump_60
              case intro assump_62 assump_63 =>
                have assump_95 : ((p4 ∧ p4) ∨ (p0 → True)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_62
                  exact assump_62
                let assump_72 := assump_5 assump_95
                apply False.elim assump_72
            case inr assump_61 =>
              cases assump_61
              case intro assump_76 assump_77 =>
                have assump_96 : ((p4 ∧ p4) ∨ (p0 → True)) := by
                  apply Or.inr
                  intro assump_87
                  apply True.intro
                let assump_86 := assump_5 assump_96
                apply False.elim assump_86
          case inr assump_57 =>
            apply False.elim assump_57


variable (p1 p6 p3 p4 p7 : Prop)
theorem file55_113116 : ((((((p6 ∧ p3) → (p4 ∨ p6)) ∨ ((p7 → False) ∧ (False → True))) → False) ∧ ((((p1 ∧ True) ∧ (p3 → False)) → ((p3 ∧ p3) → False)) → False)) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    have assump_52 : (((p1 ∧ True) ∧ (p3 → False)) → ((p3 ∧ p3) → False)) := by
      intro assump_27
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        cases assump_27
        case intro assump_35 assump_36 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            have assump_53 : p3 := by
              exact assump_30
            let assump_45 := assump_36 assump_53
            apply False.elim assump_45
    let assump_26 := assump_21 assump_52
    apply False.elim assump_26


variable (p7 p6 p4 : Prop)
theorem file55_113942 : ((((((True ∨ p6) → False) → False) → (((False → False) → (False → p7)) ∨ ((p7 → p4) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p6) → False) → False) → (((False → False) → (False → p7)) ∨ ((p7 → p4) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p7 p6 p3 p2 : Prop)
theorem file55_114422 : ((((((False ∧ p3) ∧ (p3 → p5)) ∧ ((p7 ∧ False) ∨ (p6 → p6))) ∧ (((False ∨ p5) → False) ∨ ((p7 → False) → False))) ∧ ((((p3 ∧ p6) → False) → False) → (((p2 → p5) ∧ (p3 → p6)) → False))) → False) := by
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
            apply False.elim assump_10


variable (p2 p6 p3 p4 p0 p7 : Prop)
theorem file55_115035 : ((((((p3 ∧ p7) ∧ (p3 → False)) → False) → False) ∧ ((((p2 ∨ p6) → (p3 ∧ p2)) ∧ ((p3 ∧ p6) → False)) ∧ (((p0 ∨ p0) ∧ (p6 ∨ p4)) ∨ ((p4 → p6) ∧ (False ∧ p4))))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_15
        case inl assump_22 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            cases assump_24
            case inl assump_26 =>
              cases assump_25
              case inl assump_30 =>
                have assump_150 : (((p3 ∧ p7) ∧ (p3 → False)) → False) := by
                  intro assump_42
                  cases assump_42
                  case intro assump_43 assump_44 =>
                    cases assump_43
                    case intro assump_45 assump_46 =>
                      have assump_151 : p3 := by
                        exact assump_45
                      let assump_53 := assump_44 assump_151
                      apply False.elim assump_53
                let assump_41 := assump_10 assump_150
                apply False.elim assump_41
              case inr assump_31 =>
                have assump_152 : (((p3 ∧ p7) ∧ (p3 → False)) → False) := by
                  intro assump_67
                  cases assump_67
                  case intro assump_68 assump_69 =>
                    cases assump_68
                    case intro assump_70 assump_71 =>
                      have assump_153 : p3 := by
                        exact assump_70
                      let assump_78 := assump_69 assump_153
                      apply False.elim assump_78
                let assump_66 := assump_10 assump_152
                apply False.elim assump_66
            case inr assump_27 =>
              cases assump_25
              case inl assump_87 =>
                have assump_154 : (((p3 ∧ p7) ∧ (p3 → False)) → False) := by
                  intro assump_99
                  cases assump_99
                  case intro assump_100 assump_101 =>
                    cases assump_100
                    case intro assump_102 assump_103 =>
                      have assump_155 : p3 := by
                        exact assump_102
                      let assump_110 := assump_101 assump_155
                      apply False.elim assump_110
                let assump_98 := assump_10 assump_154
                apply False.elim assump_98
              case inr assump_88 =>
                have assump_156 : (((p3 ∧ p7) ∧ (p3 → False)) → False) := by
                  intro assump_124
                  cases assump_124
                  case intro assump_125 assump_126 =>
                    cases assump_125
                    case intro assump_127 assump_128 =>
                      have assump_157 : p3 := by
                        exact assump_127
                      let assump_135 := assump_126 assump_157
                      apply False.elim assump_135
                let assump_123 := assump_10 assump_156
                apply False.elim assump_123
        case inr assump_23 =>
          cases assump_23
          case intro assump_142 assump_143 =>
            cases assump_143
            case intro assump_146 assump_147 =>
              apply False.elim assump_146


variable (p0 p3 p4 p5 p7 p2 p1 : Prop)
theorem file55_118457 : (((((p1 ∧ False) ∧ (p5 → p4)) ∨ ((p3 ∨ p4) ∧ (True → False))) → False) ∧ ((((p2 ∧ False) ∨ (p0 ∧ False)) → ((p1 → False) ∧ (p4 → p3))) → (((p0 → False) ∨ (p5 ∧ p7)) → ((False → p4) ∨ (p4 → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        have assump_54 : True := by
          apply True.intro
        let assump_20 := assump_13 assump_54
        apply False.elim assump_20
      case inr assump_15 =>
        have assump_55 : True := by
          apply True.intro
        let assump_28 := assump_13 assump_55
        apply False.elim assump_28
  intro assump_32
  intro assump_33
  cases assump_33
  case inl assump_34 =>
    apply Or.inl
    intro assump_40
    apply False.elim assump_40
  case inr assump_35 =>
    cases assump_35
    case intro assump_43 assump_44 =>
      apply Or.inl
      intro assump_51
      apply False.elim assump_51


variable (p0 p5 p6 p1 p7 p4 p3 : Prop)
theorem file55_119695 : ((((((p0 ∧ p5) → False) ∨ ((p1 → p6) → False)) ∧ (((p5 ∨ p1) → (True ∧ True)) → False)) ∧ ((((p4 ∨ False) ∨ (p6 ∨ p6)) → False) ∨ (((p3 ∧ False) → False) ∨ ((p7 ∧ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_12 =>
          have assump_72 : ((p5 ∨ p1) → (True ∧ True)) := by
            intro assump_18
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_17 := assump_5 assump_72
          apply False.elim assump_17
        case inr assump_13 =>
          cases assump_13
          case inl assump_22 =>
            have assump_73 : ((p5 ∨ p1) → (True ∧ True)) := by
              intro assump_28
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_27 := assump_5 assump_73
            apply False.elim assump_27
          case inr assump_23 =>
            have assump_74 : ((p5 ∨ p1) → (True ∧ True)) := by
              intro assump_36
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_35 := assump_5 assump_74
            apply False.elim assump_35
      case inr assump_7 =>
        cases assump_3
        case inl assump_44 =>
          have assump_75 : ((p5 ∨ p1) → (True ∧ True)) := by
            intro assump_50
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_49 := assump_5 assump_75
          apply False.elim assump_49
        case inr assump_45 =>
          cases assump_45
          case inl assump_54 =>
            have assump_76 : ((p5 ∨ p1) → (True ∧ True)) := by
              intro assump_60
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_59 := assump_5 assump_76
            apply False.elim assump_59
          case inr assump_55 =>
            have assump_77 : ((p5 ∨ p1) → (True ∧ True)) := by
              intro assump_68
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_67 := assump_5 assump_77
            apply False.elim assump_67


variable (p1 p5 p7 p0 p2 : Prop)
theorem file55_122097 : ((((((False ∨ False) ∨ (p2 → p1)) → False) ∧ (((False → False) ∧ (p2 → True)) → False)) ∨ ((((p0 → p2) ∧ (p5 → False)) → ((False ∨ p1) → (p1 ∨ p7))) → False)) → False) := by
  intro assump_19
  cases assump_19
  case inl assump_20 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      have assump_56 : ((False → False) ∧ (p2 → True)) := by
        apply And.intro
        intro assump_29
        apply False.elim assump_29
        intro assump_32
        apply True.intro
      let assump_28 := assump_23 assump_56
      apply False.elim assump_28
  case inr assump_21 =>
    have assump_57 : (((p0 → p2) ∧ (p5 → False)) → ((False ∨ p1) → (p1 ∨ p7))) := by
      intro assump_39
      intro assump_40
      cases assump_40
      case inl assump_41 =>
        apply False.elim assump_41
      case inr assump_42 =>
        cases assump_39
        case intro assump_47 assump_48 =>
          apply Or.inl
          exact assump_42
    let assump_38 := assump_21 assump_57
    apply False.elim assump_38


variable (p3 p6 p2 p0 p7 p1 : Prop)
theorem file55_123171 : (((((p3 ∧ p6) → False) → False) → (((p1 → True) → False) ∨ ((p6 → False) ∧ (p1 → True)))) → ((((True → False) → (p6 ∨ p3)) ∧ ((p1 ∨ False) ∧ (p7 ∧ p6))) ∨ (((p2 → p2) → (p7 ∨ True)) ∨ ((p0 → True) → (p2 ∨ True))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_11
  apply Or.inr
  apply True.intro


variable (p4 p7 p2 p3 p5 p0 p1 p6 : Prop)
theorem file55_123557 : (((((p6 ∨ p6) → (p6 → p0)) → False) → False) → ((((True ∨ p3) → False) → ((p1 ∨ p7) ∧ (p4 → False))) ∨ (((p4 ∧ p4) ∧ (False → False)) ∨ ((p2 → p5) ∧ (p4 ∧ p4))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  have assump_20 : (True ∨ p3) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_4 assump_20
  apply False.elim assump_7
  intro assump_11
  have assump_21 : (True ∨ p3) := by
    apply Or.inl
    apply True.intro
  let assump_16 := assump_4 assump_21
  apply False.elim assump_16


variable (p2 p6 p4 p1 p5 p7 p0 : Prop)
theorem file55_124156 : ((((((p0 → False) → (p0 → p7)) ∨ ((p4 → False) ∨ (p4 ∧ p5))) ∨ (((False ∧ p7) ∨ (p5 ∨ p0)) → False)) → ((((p2 ∧ p0) → (True ∨ p4)) ∧ ((False ∧ True) ∧ (p0 ∧ p2))) ∧ (((p6 → False) ∨ (False ∧ p6)) ∧ ((p1 → False) ∨ (p6 → False))))) → False) := by
  intro assump_1
  have assump_23 : ((((p0 → False) → (p0 → p7)) ∨ ((p4 → False) ∨ (p4 ∧ p5))) ∨ (((False ∧ p7) ∨ (p5 ∨ p0)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_24 : p0 := by
      exact assump_6
    let assump_11 := assump_5 assump_24
    apply False.elim assump_11
  let assump_4 := assump_1 assump_23
  let assump_15 := And.left assump_4
  let assump_16 := And.right assump_15
  let assump_18 := And.left assump_16
  let assump_19 := And.left assump_18
  apply False.elim assump_19


variable (p4 p0 p2 p5 p6 p3 p1 : Prop)
theorem file55_125018 : (((((p3 ∨ p6) → False) ∧ ((p1 ∧ False) ∧ (p2 → False))) ∧ (((p3 ∧ False) ∨ (p5 → False)) → False)) → ((((p4 ∨ False) ∨ (False → False)) → False) ∧ (((p0 ∧ p4) → False) → ((p5 → p1) → False)))) := by
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
          cases assump_12
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              apply False.elim assump_18
    case inr assump_6 =>
      apply False.elim assump_6
  case inr assump_4 =>
    cases assump_1
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
  intro assump_41
  intro assump_42
  cases assump_1
  case intro assump_47 assump_48 =>
    cases assump_47
    case intro assump_49 assump_50 =>
      cases assump_50
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          apply False.elim assump_56


variable (p3 p4 p5 p6 p0 p1 p7 p2 : Prop)
theorem file55_126415 : (((((False ∨ True) ∧ (p1 ∧ p7)) ∨ ((p6 ∧ p0) ∧ (p0 ∨ p1))) ∧ (((p3 ∨ p5) → (False → p0)) ∧ ((p5 ∧ p6) ∧ (p3 ∧ False)))) → ((((p4 → False) ∧ (True ∧ p3)) ∨ ((p2 → p1) → (True ∧ p5))) → (((True ∨ p2) ∧ (p0 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_1
            case intro assump_24 assump_25 =>
              cases assump_24
              case inl assump_26 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case inl assump_30 =>
                    apply False.elim assump_30
                  case inr assump_31 =>
                    cases assump_29
                    case intro assump_36 assump_37 =>
                      cases assump_25
                      case intro assump_42 assump_43 =>
                        cases assump_43
                        case intro assump_46 assump_47 =>
                          cases assump_46
                          case intro assump_48 assump_49 =>
                            cases assump_47
                            case intro assump_54 assump_55 =>
                              apply False.elim assump_55
              case inr assump_27 =>
                cases assump_27
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    cases assump_61
                    case inl assump_68 =>
                      cases assump_25
                      case intro assump_72 assump_73 =>
                        cases assump_73
                        case intro assump_76 assump_77 =>
                          cases assump_76
                          case intro assump_78 assump_79 =>
                            cases assump_77
                            case intro assump_84 assump_85 =>
                              apply False.elim assump_85
                    case inr assump_69 =>
                      cases assump_25
                      case intro assump_92 assump_93 =>
                        cases assump_93
                        case intro assump_96 assump_97 =>
                          cases assump_96
                          case intro assump_98 assump_99 =>
                            cases assump_97
                            case intro assump_104 assump_105 =>
                              apply False.elim assump_105
      case inr assump_13 =>
        cases assump_1
        case intro assump_112 assump_113 =>
          cases assump_112
          case inl assump_114 =>
            cases assump_114
            case intro assump_116 assump_117 =>
              cases assump_116
              case inl assump_118 =>
                apply False.elim assump_118
              case inr assump_119 =>
                cases assump_117
                case intro assump_124 assump_125 =>
                  cases assump_113
                  case intro assump_130 assump_131 =>
                    cases assump_131
                    case intro assump_134 assump_135 =>
                      cases assump_134
                      case intro assump_136 assump_137 =>
                        cases assump_135
                        case intro assump_142 assump_143 =>
                          apply False.elim assump_143
          case inr assump_115 =>
            cases assump_115
            case intro assump_148 assump_149 =>
              cases assump_148
              case intro assump_150 assump_151 =>
                cases assump_149
                case inl assump_156 =>
                  cases assump_113
                  case intro assump_160 assump_161 =>
                    cases assump_161
                    case intro assump_164 assump_165 =>
                      cases assump_164
                      case intro assump_166 assump_167 =>
                        cases assump_165
                        case intro assump_172 assump_173 =>
                          apply False.elim assump_173
                case inr assump_157 =>
                  cases assump_113
                  case intro assump_180 assump_181 =>
                    cases assump_181
                    case intro assump_184 assump_185 =>
                      cases assump_184
                      case intro assump_186 assump_187 =>
                        cases assump_185
                        case intro assump_192 assump_193 =>
                          apply False.elim assump_193
    case inr assump_7 =>
      cases assump_2
      case inl assump_202 =>
        cases assump_202
        case intro assump_204 assump_205 =>
          cases assump_205
          case intro assump_208 assump_209 =>
            cases assump_1
            case intro assump_214 assump_215 =>
              cases assump_214
              case inl assump_216 =>
                cases assump_216
                case intro assump_218 assump_219 =>
                  cases assump_218
                  case inl assump_220 =>
                    apply False.elim assump_220
                  case inr assump_221 =>
                    cases assump_219
                    case intro assump_226 assump_227 =>
                      cases assump_215
                      case intro assump_232 assump_233 =>
                        cases assump_233
                        case intro assump_236 assump_237 =>
                          cases assump_236
                          case intro assump_238 assump_239 =>
                            cases assump_237
                            case intro assump_244 assump_245 =>
                              apply False.elim assump_245
              case inr assump_217 =>
                cases assump_217
                case intro assump_250 assump_251 =>
                  cases assump_250
                  case intro assump_252 assump_253 =>
                    cases assump_251
                    case inl assump_258 =>
                      cases assump_215
                      case intro assump_262 assump_263 =>
                        cases assump_263
                        case intro assump_266 assump_267 =>
                          cases assump_266
                          case intro assump_268 assump_269 =>
                            cases assump_267
                            case intro assump_274 assump_275 =>
                              apply False.elim assump_275
                    case inr assump_259 =>
                      cases assump_215
                      case intro assump_282 assump_283 =>
                        cases assump_283
                        case intro assump_286 assump_287 =>
                          cases assump_286
                          case intro assump_288 assump_289 =>
                            cases assump_287
                            case intro assump_294 assump_295 =>
                              apply False.elim assump_295
      case inr assump_203 =>
        cases assump_1
        case intro assump_302 assump_303 =>
          cases assump_302
          case inl assump_304 =>
            cases assump_304
            case intro assump_306 assump_307 =>
              cases assump_306
              case inl assump_308 =>
                apply False.elim assump_308
              case inr assump_309 =>
                cases assump_307
                case intro assump_314 assump_315 =>
                  cases assump_303
                  case intro assump_320 assump_321 =>
                    cases assump_321
                    case intro assump_324 assump_325 =>
                      cases assump_324
                      case intro assump_326 assump_327 =>
                        cases assump_325
                        case intro assump_332 assump_333 =>
                          apply False.elim assump_333
          case inr assump_305 =>
            cases assump_305
            case intro assump_338 assump_339 =>
              cases assump_338
              case intro assump_340 assump_341 =>
                cases assump_339
                case inl assump_346 =>
                  cases assump_303
                  case intro assump_350 assump_351 =>
                    cases assump_351
                    case intro assump_354 assump_355 =>
                      cases assump_354
                      case intro assump_356 assump_357 =>
                        cases assump_355
                        case intro assump_362 assump_363 =>
                          apply False.elim assump_363
                case inr assump_347 =>
                  cases assump_303
                  case intro assump_370 assump_371 =>
                    cases assump_371
                    case intro assump_374 assump_375 =>
                      cases assump_374
                      case intro assump_376 assump_377 =>
                        cases assump_375
                        case intro assump_382 assump_383 =>
                          apply False.elim assump_383


variable (p4 p7 p3 p6 p5 p1 p2 : Prop)
theorem file55_135798 : (((((p2 ∨ True) → (p5 ∧ p4)) → False) → (((p6 ∧ p7) ∧ (False ∧ p1)) → ((p3 → p2) ∧ (p1 ∧ p7)))) ∨ ((((p5 → False) → (p2 ∨ p1)) ∨ ((p2 → False) → False)) ∨ (((True ∧ p4) → (p6 → False)) ∨ ((p6 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
  apply And.intro
  cases assump_2
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_19
      case intro assump_26 assump_27 =>
        apply False.elim assump_26
  cases assump_2
  case intro assump_30 assump_31 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_31
      case intro assump_38 assump_39 =>
        apply False.elim assump_38


variable (p6 p7 p5 p2 p0 p4 : Prop)
theorem file55_136797 : ((((((p6 → False) → False) ∧ ((p2 ∧ p7) ∨ (p0 → False))) → (((p4 → p5) → (True ∨ p0)) ∨ ((True ∨ p5) ∨ (p6 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p6 → False) → False) ∧ ((p2 ∧ p7) ∨ (p0 → False))) → (((p4 → p5) → (True ∨ p0)) ∨ ((True ∨ p5) ∨ (p6 ∨ False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          apply Or.inl
          apply True.intro
      case inr assump_11 =>
        apply Or.inl
        intro assump_23
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p1 p6 p3 p2 p4 : Prop)
theorem file55_137631 : ((((((p4 → False) ∧ (p2 ∧ p6)) → False) ∧ (((p4 → False) → False) ∧ ((p3 → p2) ∧ (False ∨ False)))) ∧ ((((p1 → p3) ∧ (p1 → False)) ∨ ((p7 ∧ p2) ∨ (p7 ∨ False))) → (((p1 ∨ p1) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            apply False.elim assump_16
          case inr assump_17 =>
            apply False.elim assump_17


variable (p0 p7 p4 p3 p6 p5 : Prop)
theorem file55_138316 : (((((p6 ∧ p7) → (p6 ∧ p5)) → ((False ∨ True) ∨ (p4 → p4))) ∨ (((p6 → False) ∨ (p3 → False)) → False)) ∨ ((((p3 ∨ p7) → False) ∨ ((p0 ∧ p6) ∧ (p4 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p0 p4 p7 p5 p2 p1 p6 : Prop)
theorem file55_138647 : (((((p4 ∨ p0) ∨ (p7 → p1)) ∧ ((p5 ∧ False) ∧ (p2 → p0))) → False) ∨ ((((True → False) → (p1 ∧ p0)) ∨ ((p7 ∨ p2) ∧ (p7 ∧ p5))) ∧ (((p7 ∧ True) → (p2 → False)) ∨ ((p0 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13
      case inr assump_7 =>
        cases assump_3
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
    case inr assump_5 =>
      cases assump_3
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          apply False.elim assump_33


variable (p6 p4 p5 p1 p2 p0 : Prop)
theorem file55_139635 : ((((((p0 → p0) ∧ (p2 → False)) → False) ∧ (((False → p5) → False) ∧ ((p4 ∨ p6) ∧ (p2 ∨ True)))) ∨ ((((True → p1) ∧ (p4 ∧ False)) → False) → False)) → False) := by
  intro assump_6
  cases assump_6
  case inl assump_7 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_18
            case inl assump_23 =>
              have assump_88 : (False → p5) := by
                intro assump_30
                apply False.elim assump_30
              let assump_29 := assump_13 assump_88
              apply False.elim assump_29
            case inr assump_24 =>
              have assump_89 : (False → p5) := by
                intro assump_40
                apply False.elim assump_40
              let assump_39 := assump_13 assump_89
              apply False.elim assump_39
          case inr assump_20 =>
            cases assump_18
            case inl assump_48 =>
              have assump_90 : (False → p5) := by
                intro assump_55
                apply False.elim assump_55
              let assump_54 := assump_13 assump_90
              apply False.elim assump_54
            case inr assump_49 =>
              have assump_91 : (False → p5) := by
                intro assump_65
                apply False.elim assump_65
              let assump_64 := assump_13 assump_91
              apply False.elim assump_64
  case inr assump_8 =>
    have assump_92 : (((True → p1) ∧ (p4 ∧ False)) → False) := by
      intro assump_74
      cases assump_74
      case intro assump_75 assump_76 =>
        cases assump_76
        case intro assump_79 assump_80 =>
          apply False.elim assump_80
    let assump_73 := assump_8 assump_92
    apply False.elim assump_73


variable (p1 p5 p2 p0 p6 p4 p3 : Prop)
theorem file55_141599 : ((((((p3 ∨ p5) ∧ (p5 ∨ p2)) ∧ ((p4 ∨ True) → False)) ∨ (((p1 ∧ p2) ∧ (True → False)) ∨ ((True → False) → (p0 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p3 ∨ p5) ∧ (p5 ∨ p2)) ∧ ((p4 ∨ True) → False)) ∨ (((p1 ∧ p2) ∧ (True → False)) ∨ ((True → False) → (p0 ∧ p6)))) := by
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply And.intro
    have assump_22 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
    have assump_23 : True := by
      apply True.intro
    let assump_14 := assump_5 assump_23
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 p5 p0 p6 p1 : Prop)
theorem file55_142344 : (((((False ∧ p0) → False) ∧ ((p3 ∨ p3) → (p6 ∨ p1))) ∧ (((False → False) → False) ∧ ((True ∧ p3) ∨ (p5 ∨ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            have assump_44 : (False → False) := by
              intro assump_24
              apply False.elim assump_24
            let assump_23 := assump_10 assump_44
            apply False.elim assump_23
        case inr assump_15 =>
          cases assump_15
          case inl assump_30 =>
            have assump_45 : (False → False) := by
              intro assump_36
              apply False.elim assump_36
            let assump_35 := assump_10 assump_45
            apply False.elim assump_35
          case inr assump_31 =>
            apply False.elim assump_31


variable (p7 p0 p1 p3 p5 p2 p6 p4 : Prop)
theorem file55_143427 : (((((p2 ∧ p2) ∧ (True ∨ p3)) ∧ ((p5 → False) → (p2 → False))) ∧ (((p6 ∨ p1) ∨ (p4 ∨ p5)) → ((p7 ∨ p3) ∧ (p1 → p1)))) → ((((p1 → p0) → (True ∨ False)) ∨ ((p0 ∧ p7) ∧ (p1 → p5))) ∨ (((True → p1) → (p5 → True)) → ((p2 → False) ∧ (p2 ∨ False))))) := by
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
          case inl assump_14 =>
            apply Or.inl
            apply Or.inl
            intro assump_22
            apply Or.inl
            apply True.intro
          case inr assump_15 =>
            apply Or.inl
            apply Or.inl
            intro assump_31
            apply Or.inl
            apply True.intro


variable (p0 p6 p5 p3 p1 p2 : Prop)
theorem file55_144334 : (((((p6 → p6) → (True → False)) ∧ ((p5 ∧ p3) → False)) → (((p2 ∧ p5) → False) → False)) ∨ ((((p3 ∨ False) → (p3 → p2)) ∨ ((p5 ∧ True) ∧ (True → False))) ∨ (((p1 ∨ p0) ∨ (False ∨ p3)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_20 : (p6 → p6) := by
      intro assump_13
      exact assump_13
    let assump_12 := assump_5 assump_20
    have assump_21 : True := by
      apply True.intro
    let assump_16 := assump_12 assump_21
    apply False.elim assump_16


