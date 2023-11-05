variable (p5 p1 p4 p6 p3 p0 p7 p2 : Prop)
theorem file80_50 : ((((((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) → False) ∧ ((((p1 → False) ∨ (p4 → p7)) ∧ ((p3 ∧ p0) ∨ (p7 ∨ True))) ∨ (((p2 ∨ p1) ∧ (True → False)) → False))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_17
    case inl assump_20 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_22
        case inl assump_24 =>
          cases assump_23
          case inl assump_28 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              have assump_255 : (((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) := by
                intro assump_40
                apply And.intro
                have assump_256 : (False → p2) := by
                  intro assump_44
                  apply False.elim assump_44
                let assump_43 := assump_40 assump_256
                apply False.elim assump_43
                intro assump_50
                have assump_257 : (False → p2) := by
                  intro assump_56
                  apply False.elim assump_56
                let assump_55 := assump_40 assump_257
                apply False.elim assump_55
              let assump_39 := assump_16 assump_255
              apply False.elim assump_39
          case inr assump_29 =>
            cases assump_29
            case inl assump_65 =>
              have assump_258 : (((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) := by
                intro assump_72
                apply And.intro
                have assump_259 : (False → p2) := by
                  intro assump_76
                  apply False.elim assump_76
                let assump_75 := assump_72 assump_259
                apply False.elim assump_75
                intro assump_82
                have assump_260 : (False → p2) := by
                  intro assump_88
                  apply False.elim assump_88
                let assump_87 := assump_72 assump_260
                apply False.elim assump_87
              let assump_71 := assump_16 assump_258
              apply False.elim assump_71
            case inr assump_66 =>
              have assump_261 : (((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) := by
                intro assump_101
                apply And.intro
                have assump_262 : (False → p2) := by
                  intro assump_105
                  apply False.elim assump_105
                let assump_104 := assump_101 assump_262
                apply False.elim assump_104
                intro assump_111
                have assump_263 : (False → p2) := by
                  intro assump_117
                  apply False.elim assump_117
                let assump_116 := assump_101 assump_263
                apply False.elim assump_116
              let assump_100 := assump_16 assump_261
              apply False.elim assump_100
        case inr assump_25 =>
          cases assump_23
          case inl assump_128 =>
            cases assump_128
            case intro assump_130 assump_131 =>
              have assump_264 : (((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) := by
                intro assump_140
                apply And.intro
                have assump_265 : (False → p2) := by
                  intro assump_144
                  apply False.elim assump_144
                let assump_143 := assump_140 assump_265
                apply False.elim assump_143
                intro assump_150
                have assump_266 : (False → p2) := by
                  intro assump_156
                  apply False.elim assump_156
                let assump_155 := assump_140 assump_266
                apply False.elim assump_155
              let assump_139 := assump_16 assump_264
              apply False.elim assump_139
          case inr assump_129 =>
            cases assump_129
            case inl assump_165 =>
              have assump_267 : (((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) := by
                intro assump_172
                apply And.intro
                have assump_268 : (False → p2) := by
                  intro assump_176
                  apply False.elim assump_176
                let assump_175 := assump_172 assump_268
                apply False.elim assump_175
                intro assump_182
                have assump_269 : (False → p2) := by
                  intro assump_188
                  apply False.elim assump_188
                let assump_187 := assump_172 assump_269
                apply False.elim assump_187
              let assump_171 := assump_16 assump_267
              apply False.elim assump_171
            case inr assump_166 =>
              have assump_270 : (((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) := by
                intro assump_201
                apply And.intro
                have assump_271 : (False → p2) := by
                  intro assump_205
                  apply False.elim assump_205
                let assump_204 := assump_201 assump_271
                apply False.elim assump_204
                intro assump_211
                have assump_272 : (False → p2) := by
                  intro assump_217
                  apply False.elim assump_217
                let assump_216 := assump_201 assump_272
                apply False.elim assump_216
              let assump_200 := assump_16 assump_270
              apply False.elim assump_200
    case inr assump_21 =>
      have assump_273 : (((False → p2) → False) → ((p5 ∨ p5) ∧ (p0 → p6))) := by
        intro assump_230
        apply And.intro
        have assump_274 : (False → p2) := by
          intro assump_234
          apply False.elim assump_234
        let assump_233 := assump_230 assump_274
        apply False.elim assump_233
        intro assump_240
        have assump_275 : (False → p2) := by
          intro assump_246
          apply False.elim assump_246
        let assump_245 := assump_230 assump_275
        apply False.elim assump_245
      let assump_229 := assump_16 assump_273
      apply False.elim assump_229


variable (p5 p3 p2 p1 p6 p7 : Prop)
theorem file80_6203 : (((((p7 → False) ∧ (p2 ∨ p6)) → ((p1 → p1) → False)) → False) → ((((False ∧ p5) → False) → ((True → p7) → False)) → (((p1 → False) → False) → ((p1 ∧ False) → (p3 ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p5 p7 p4 p2 p6 p3 : Prop)
theorem file80_6592 : (((((p7 → False) ∨ (p6 → False)) ∧ ((p3 ∨ True) → False)) → False) ∨ ((((p5 ∧ p2) ∧ (p3 → False)) ∧ ((p4 → False) → False)) → (((p5 → p7) ∧ (p2 → True)) ∨ ((p3 → p5) ∧ (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_22 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_10 := assump_3 assump_22
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_23 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_18 := assump_3 assump_23
      apply False.elim assump_18


variable (p3 p5 p0 p4 p6 p7 p2 : Prop)
theorem file80_7322 : (((((p4 ∨ p4) → (p6 ∧ p3)) → False) ∧ (((True → p4) ∨ (p2 ∨ p6)) ∧ ((p0 ∧ False) ∧ (p6 ∨ p0)))) → ((((p7 ∧ p3) → False) ∨ ((p4 → p4) → False)) ∨ (((False → p0) → (p7 ∨ p6)) → ((p5 → False) → (p5 → False))))) := by
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
            apply False.elim assump_15
      case inr assump_9 =>
        cases assump_9
        case inl assump_20 =>
          cases assump_7
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
        case inr assump_21 =>
          cases assump_7
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_37


variable (p0 p5 p7 p2 p4 p3 p1 p6 : Prop)
theorem file80_8425 : (((((p3 ∧ p2) ∨ (p1 ∨ p2)) → ((p6 ∨ p0) → False)) → False) → ((((True ∧ p1) ∧ (p7 → p0)) ∨ ((p6 ∧ p2) → (p0 ∨ p6))) ∨ (((p7 → p4) ∨ (p5 → False)) ∨ ((p1 → False) ∨ (p5 ∨ True))))) := by
  intro assump_5
  apply Or.inl
  apply Or.inr
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply Or.inr
    exact assump_9


variable (p6 p7 p1 p0 : Prop)
theorem file80_8817 : (((((True ∧ False) → (True → p0)) → False) ∧ (((p1 ∧ p1) ∨ (p0 → p7)) ∨ ((False ∨ p1) → False))) → ((((p7 ∧ p6) → False) ∧ ((p1 → p0) ∧ (False → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              have assump_77 : ((True ∧ False) → (True → p0)) := by
                intro assump_30
                intro assump_31
                cases assump_30
                case intro assump_34 assump_35 =>
                  apply False.elim assump_35
              let assump_29 := assump_13 assump_77
              apply False.elim assump_29
          case inr assump_20 =>
            have assump_78 : ((True ∧ False) → (True → p0)) := by
              intro assump_47
              intro assump_48
              cases assump_47
              case intro assump_51 assump_52 =>
                apply False.elim assump_52
            let assump_46 := assump_13 assump_78
            apply False.elim assump_46
        case inr assump_18 =>
          have assump_79 : ((True ∧ False) → (True → p0)) := by
            intro assump_64
            intro assump_65
            cases assump_64
            case intro assump_68 assump_69 =>
              apply False.elim assump_69
          let assump_63 := assump_13 assump_79
          apply False.elim assump_63


variable (p7 p0 p1 p6 p4 : Prop)
theorem file80_10498 : (((((p6 ∨ p0) ∨ (p0 → p0)) → False) → False) ∨ ((((p7 → p0) → (True ∨ p0)) → ((True ∨ p7) ∧ (p7 ∨ p6))) ∨ (((p4 ∨ p1) ∧ (p7 ∧ p7)) ∨ ((p1 → False) ∨ (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p6 ∨ p0) ∨ (p0 → p0)) := by
    apply Or.inr
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p6 p1 p0 p5 p3 p7 : Prop)
theorem file80_10934 : (((((p1 ∧ False) ∨ (p6 ∧ p7)) → False) ∧ (((True → p7) → (p3 → p0)) → False)) → ((((p0 ∧ p2) ∧ (p7 → False)) → ((p7 → False) → False)) ∨ (((p1 → p0) → (p6 → p3)) ∨ ((False ∧ p5) → (p6 ∨ p1))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_36 : ((True → p7) → (p3 → p0)) := by
          intro assump_27
          intro assump_28
          exact assump_14
        let assump_26 := assump_3 assump_36
        apply False.elim assump_26


variable (p4 p1 p6 p5 p3 p0 p7 : Prop)
theorem file80_11653 : (((((True → False) ∧ (p6 ∨ True)) → ((p3 → p1) → (p4 ∧ p0))) ∨ (((p7 → False) ∨ (p4 → False)) ∨ ((p1 → p7) ∧ (p3 → False)))) ∧ ((((False ∧ p4) ∧ (p1 ∧ p6)) → ((p6 → False) ∧ (False ∨ p7))) ∨ (((p5 → False) → (True ∧ p4)) ∨ ((p5 → p4) → False)))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_61 : True := by
        apply True.intro
      let assump_14 := assump_5 assump_61
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_62 : True := by
        apply True.intro
      let assump_20 := assump_5 assump_62
      apply False.elim assump_20
  cases assump_1
  case intro assump_26 assump_27 =>
    cases assump_27
    case inl assump_30 =>
      have assump_63 : True := by
        apply True.intro
      let assump_35 := assump_26 assump_63
      apply False.elim assump_35
    case inr assump_31 =>
      have assump_64 : True := by
        apply True.intro
      let assump_41 := assump_26 assump_64
      apply False.elim assump_41
  apply Or.inl
  intro assump_45
  apply And.intro
  intro assump_46
  cases assump_45
  case intro assump_49 assump_50 =>
    cases assump_49
    case intro assump_51 assump_52 =>
      apply False.elim assump_51
  cases assump_45
  case intro assump_55 assump_56 =>
    cases assump_55
    case intro assump_57 assump_58 =>
      apply False.elim assump_57


variable (p5 p7 : Prop)
theorem file80_13181 : ((((((p5 ∨ p7) ∨ (True ∧ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p5 ∨ p7) ∨ (True ∧ True)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p5 ∨ p7) ∨ (True ∧ True)) := by
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p1 p5 p6 p0 p7 p4 : Prop)
theorem file80_13703 : (((((True → False) → (p5 → False)) ∧ ((True ∧ False) → False)) ∨ (((True ∧ p2) → False) ∧ ((p6 ∧ p4) → (p0 → False)))) ∨ ((((p0 → p7) ∨ (p0 ∨ p6)) → False) ∧ (((p0 → p1) → False) ∨ ((False ∨ p0) → (p2 → p6))))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  have assump_18 : True := by
    apply True.intro
  let assump_7 := assump_1 assump_18
  apply False.elim assump_7
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    apply False.elim assump_13


variable (p3 p6 p2 p1 p7 p0 p5 p4 : Prop)
theorem file80_14287 : (((((p0 → p6) → (p6 → False)) → ((p7 ∨ False) ∨ (True ∨ p4))) ∨ (((p4 ∧ p7) ∧ (p3 ∨ p3)) → ((p6 ∨ p1) → (p3 ∧ p4)))) ∨ ((((p5 → True) → False) ∨ ((p7 ∨ p2) → False)) ∧ (((p7 → False) → (p1 → p5)) ∧ ((p0 ∨ p6) ∨ (False ∧ p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p3 p2 p4 p7 : Prop)
theorem file80_14671 : (((((p2 ∨ True) → False) → ((p2 ∨ p7) ∨ (p3 → p2))) ∧ (((False → False) ∧ (True → False)) → False)) ∨ ((((p3 ∨ p4) ∨ (True → False)) → False) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply Or.inr
  intro assump_4
  have assump_23 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_8 := assump_1 assump_23
  apply False.elim assump_8
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_24 : True := by
      apply True.intro
    let assump_19 := assump_14 assump_24
    apply False.elim assump_19


variable (p7 p6 p2 p4 p3 p5 : Prop)
theorem file80_15310 : ((((((p5 → p2) ∨ (p7 ∧ p5)) → ((p7 ∧ p3) ∨ (False ∧ p3))) → False) ∧ ((((p5 ∨ p6) → False) ∧ ((False ∧ p4) ∧ (p6 → p7))) ∧ (((p7 ∨ True) → (p7 ∧ p2)) ∧ ((True ∧ p7) ∧ (p2 ∨ p4))))) → False) := by
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


variable (p3 p7 p6 p1 p0 p5 p2 : Prop)
theorem file80_15925 : ((((((p2 ∧ p6) ∧ (p0 → p1)) ∨ ((p5 → True) ∨ (False ∧ p5))) ∨ (((p3 ∨ p7) → False) ∧ ((p1 ∧ p0) ∧ (p2 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p2 ∧ p6) ∧ (p0 → p1)) ∨ ((p5 → True) ∨ (False ∧ p5))) ∨ (((p3 ∨ p7) → False) ∧ ((p1 ∧ p0) ∧ (p2 ∨ p2)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p4 p1 p3 p6 p2 p5 p0 p7 : Prop)
theorem file80_16431 : (((((p7 ∨ p5) ∨ (p7 ∨ p4)) → False) ∧ (((True ∨ p2) ∧ (p4 → p7)) ∨ ((p6 → p4) ∨ (False → p1)))) → ((((False ∧ p3) ∧ (p3 → p4)) ∨ ((p2 → p0) ∧ (p3 ∧ p7))) → (((p4 ∧ p1) ∧ (p2 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
      case inr assump_15 =>
        cases assump_15
        case intro assump_22 assump_23 =>
          cases assump_23
          case intro assump_26 assump_27 =>
            cases assump_1
            case intro assump_32 assump_33 =>
              cases assump_33
              case inl assump_36 =>
                cases assump_36
                case intro assump_38 assump_39 =>
                  cases assump_38
                  case inl assump_40 =>
                    have assump_79 : ((p7 ∨ p5) ∨ (p7 ∨ p4)) := by
                      apply Or.inl
                      apply Or.inl
                      exact assump_27
                    let assump_48 := assump_32 assump_79
                    apply False.elim assump_48
                  case inr assump_41 =>
                    have assump_80 : ((p7 ∨ p5) ∨ (p7 ∨ p4)) := by
                      apply Or.inl
                      apply Or.inl
                      exact assump_27
                    let assump_59 := assump_32 assump_80
                    apply False.elim assump_59
              case inr assump_37 =>
                cases assump_37
                case inl assump_63 =>
                  have assump_81 : ((p7 ∨ p5) ∨ (p7 ∨ p4)) := by
                    apply Or.inl
                    apply Or.inl
                    exact assump_27
                  let assump_68 := assump_32 assump_81
                  apply False.elim assump_68
                case inr assump_64 =>
                  have assump_82 : ((p7 ∨ p5) ∨ (p7 ∨ p4)) := by
                    apply Or.inl
                    apply Or.inl
                    exact assump_27
                  let assump_75 := assump_32 assump_82
                  apply False.elim assump_75


variable (p4 p6 p1 : Prop)
theorem file80_18799 : ((((((p6 ∧ p1) ∧ (True → False)) ∧ ((p4 ∨ p4) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p6 ∧ p1) ∧ (True → False)) ∧ ((p4 ∨ p4) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_29 : True := by
            apply True.intro
          let assump_21 := assump_9 assump_29
          apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p3 p2 p5 p0 p6 p4 p7 : Prop)
theorem file80_19469 : (((((p2 → p3) → False) ∧ ((p4 → False) ∧ (p6 ∧ p2))) → (((p2 ∨ p0) ∨ (p7 ∨ p3)) ∨ ((p0 ∧ p0) ∨ (p5 → p2)))) ∨ ((((False ∧ p6) → False) → ((p0 ∨ p6) ∧ (False → p4))) ∧ (((False ∧ p4) ∧ (p3 ∧ True)) ∧ ((p4 ∧ p6) ∨ (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_11


variable (p1 p4 p7 p6 p2 p3 p0 : Prop)
theorem file80_20053 : (((((False → False) ∨ (p3 ∧ p6)) ∨ ((True ∧ p2) ∨ (p3 → False))) → False) → ((((p6 ∧ p7) ∨ (True → p0)) ∧ ((p1 → False) → (True ∨ p7))) → (((p3 ∨ p4) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        have assump_40 : (((False → False) ∨ (p3 ∧ p6)) ∨ ((True ∧ p2) ∨ (p3 → False))) := by
          apply Or.inl
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
        let assump_20 := assump_1 assump_40
        apply False.elim assump_20
    case inr assump_9 =>
      have assump_41 : (((False → False) ∨ (p3 ∧ p6)) ∨ ((True ∧ p2) ∨ (p3 → False))) := by
        apply Or.inl
        apply Or.inl
        intro assump_34
        apply False.elim assump_34
      let assump_33 := assump_1 assump_41
      apply False.elim assump_33


variable (p4 p1 p0 p2 p7 : Prop)
theorem file80_21068 : ((((((p0 ∧ False) ∨ (p0 ∧ True)) ∧ ((False ∨ True) ∨ (p1 → False))) → (((p4 ∧ p7) ∨ (True → p0)) → ((p2 ∧ p7) → (p2 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_79 : ((((p0 ∧ False) ∨ (p0 ∧ True)) ∧ ((False ∨ True) ∨ (p1 → False))) → (((p4 ∧ p7) ∨ (True → p0)) → ((p2 ∧ p7) → (p2 ∨ p1)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_5
          case intro assump_22 assump_23 =>
            cases assump_22
            case inl assump_24 =>
              cases assump_24
              case intro assump_26 assump_27 =>
                apply False.elim assump_27
            case inr assump_25 =>
              cases assump_25
              case intro assump_32 assump_33 =>
                cases assump_23
                case inl assump_38 =>
                  cases assump_38
                  case inl assump_40 =>
                    apply False.elim assump_40
                  case inr assump_41 =>
                    apply Or.inl
                    exact assump_8
                case inr assump_39 =>
                  apply Or.inl
                  exact assump_8
      case inr assump_15 =>
        cases assump_5
        case intro assump_50 assump_51 =>
          cases assump_50
          case inl assump_52 =>
            cases assump_52
            case intro assump_54 assump_55 =>
              apply False.elim assump_55
          case inr assump_53 =>
            cases assump_53
            case intro assump_60 assump_61 =>
              cases assump_51
              case inl assump_66 =>
                cases assump_66
                case inl assump_68 =>
                  apply False.elim assump_68
                case inr assump_69 =>
                  apply Or.inl
                  exact assump_8
              case inr assump_67 =>
                apply Or.inl
                exact assump_8
  let assump_4 := assump_1 assump_79
  apply False.elim assump_4


variable (p3 p7 p0 p5 p4 : Prop)
theorem file80_23247 : ((((((p4 ∧ False) ∧ (p7 ∧ p0)) ∧ ((p5 ∧ p0) ∧ (p3 ∧ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 ∧ False) ∧ (p7 ∧ p0)) ∧ ((p5 ∧ p0) ∧ (p3 ∧ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p3 p5 p0 : Prop)
theorem file80_23799 : (((((True → False) → (p4 ∧ p3)) → False) ∧ (((p5 ∨ p5) → (True ∧ p5)) ∧ ((p5 ∨ p3) → (p0 ∨ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_31 : ((True → False) → (p4 ∧ p3)) := by
        intro assump_15
        apply And.intro
        have assump_32 : True := by
          apply True.intro
        let assump_18 := assump_15 assump_32
        apply False.elim assump_18
        have assump_33 : True := by
          apply True.intro
        let assump_24 := assump_15 assump_33
        apply False.elim assump_24
      let assump_14 := assump_2 assump_31
      apply False.elim assump_14


variable (p3 p5 p2 p4 p7 : Prop)
theorem file80_24559 : ((((((p2 ∧ p3) → (p7 → False)) → False) → (((p2 → False) → (p5 ∧ p4)) ∨ ((p4 → False) → False))) → False) → False) := by
  intro assump_5
  have assump_64 : ((((p2 ∧ p3) → (p7 → False)) → False) → (((p2 → False) → (p5 ∧ p4)) ∨ ((p4 → False) → False))) := by
    intro assump_9
    apply Or.inl
    intro assump_12
    apply And.intro
    have assump_65 : ((p2 ∧ p3) → (p7 → False)) := by
      intro assump_17
      intro assump_18
      cases assump_17
      case intro assump_21 assump_22 =>
        have assump_66 : p2 := by
          exact assump_21
        let assump_30 := assump_12 assump_66
        apply False.elim assump_30
    let assump_16 := assump_9 assump_65
    apply False.elim assump_16
    have assump_67 : ((p2 ∧ p3) → (p7 → False)) := by
      intro assump_41
      intro assump_42
      cases assump_41
      case intro assump_45 assump_46 =>
        have assump_68 : p2 := by
          exact assump_45
        let assump_54 := assump_12 assump_68
        apply False.elim assump_54
    let assump_40 := assump_9 assump_67
    apply False.elim assump_40
  let assump_8 := assump_5 assump_64
  apply False.elim assump_8


variable (p4 p7 p1 p3 p2 p0 p6 : Prop)
theorem file80_25763 : (((((p4 → False) ∧ (p2 → False)) ∧ ((p7 ∨ False) → False)) ∧ (((True ∨ p3) ∨ (p1 → p0)) → False)) → ((((p2 → False) ∨ (p0 → False)) → ((p1 → p2) → False)) → (((p6 ∧ p2) → (p0 ∧ p2)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_26 : ((True ∨ p3) ∨ (p1 → p0)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_22 := assump_9 assump_26
        apply False.elim assump_22


variable (p3 p0 p5 p6 p2 p4 p1 p7 : Prop)
theorem file80_26458 : (((((p0 ∨ True) → (p2 ∨ p1)) → ((p7 → False) ∧ (True → False))) → (((p1 ∨ p0) → (p1 → False)) ∨ ((p4 ∨ p3) ∧ (p4 → p5)))) ∨ ((((p6 → p3) → (p4 → p5)) ∨ ((p0 ∧ True) ∧ (p2 ∧ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_46 : ((p0 ∨ True) → (p2 ∨ p1)) := by
      intro assump_15
      cases assump_15
      case inl assump_16 =>
        apply Or.inr
        exact assump_8
      case inr assump_17 =>
        apply Or.inr
        exact assump_8
    let assump_14 := assump_1 assump_46
    let assump_22 := And.right assump_14
    have assump_47 : True := by
      apply True.intro
    let assump_24 := assump_22 assump_47
    apply False.elim assump_24
  case inr assump_9 =>
    have assump_48 : ((p0 ∨ True) → (p2 ∨ p1)) := by
      intro assump_33
      cases assump_33
      case inl assump_34 =>
        apply Or.inr
        exact assump_5
      case inr assump_35 =>
        apply Or.inr
        exact assump_5
    let assump_32 := assump_1 assump_48
    let assump_40 := And.right assump_32
    have assump_49 : True := by
      apply True.intro
    let assump_42 := assump_40 assump_49
    apply False.elim assump_42


variable (p7 p2 p4 p6 p5 p1 p0 : Prop)
theorem file80_27758 : (((((p0 ∨ True) → False) → False) → False) → ((((p0 ∧ p6) ∨ (p1 → p0)) ∧ ((True → p5) ∧ (p0 ∨ p7))) → (((p1 → p0) → False) ∨ ((False → False) ∨ (p4 ∧ p2))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_14
          case inl assump_17 =>
            apply Or.inl
            intro assump_23
            have assump_103 : (((p0 ∨ True) → False) → False) := by
              intro assump_28
              have assump_104 : (p0 ∨ True) := by
                apply Or.inl
                exact assump_17
              let assump_31 := assump_28 assump_104
              apply False.elim assump_31
            let assump_27 := assump_1 assump_103
            apply False.elim assump_27
          case inr assump_18 =>
            apply Or.inl
            intro assump_42
            have assump_105 : (((p0 ∨ True) → False) → False) := by
              intro assump_47
              have assump_106 : (p0 ∨ True) := by
                apply Or.inl
                exact assump_7
              let assump_50 := assump_47 assump_106
              apply False.elim assump_50
            let assump_46 := assump_1 assump_105
            apply False.elim assump_46
    case inr assump_6 =>
      cases assump_4
      case intro assump_59 assump_60 =>
        cases assump_60
        case inl assump_63 =>
          apply Or.inl
          intro assump_69
          have assump_107 : (((p0 ∨ True) → False) → False) := by
            intro assump_74
            have assump_108 : (p0 ∨ True) := by
              apply Or.inl
              exact assump_63
            let assump_77 := assump_74 assump_108
            apply False.elim assump_77
          let assump_73 := assump_1 assump_107
          apply False.elim assump_73
        case inr assump_64 =>
          apply Or.inl
          intro assump_88
          have assump_109 : (((p0 ∨ True) → False) → False) := by
            intro assump_93
            have assump_110 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_96 := assump_93 assump_110
            apply False.elim assump_96
          let assump_92 := assump_1 assump_109
          apply False.elim assump_92


variable (p0 p5 p1 : Prop)
theorem file80_30214 : (((((p0 ∧ p5) → (True ∨ p1)) ∧ ((True ∧ p5) → (p5 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p0 ∧ p5) → (True ∨ p1)) ∧ ((True ∧ p5) → (p5 ∨ True))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply Or.inl
      exact assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p0 p6 p4 p1 p7 : Prop)
theorem file80_30778 : ((((((True ∧ p3) → (True → True)) ∧ ((p4 ∧ p0) ∧ (p6 → False))) → (((False ∧ False) → (p1 ∧ p7)) → False)) ∧ ((((False ∧ p1) → (p7 → False)) ∨ ((p0 ∨ p0) → False)) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    have assump_28 : (((False ∧ p1) → (p7 → False)) ∨ ((p0 ∨ p0) → False)) := by
      apply Or.inl
      intro assump_17
      intro assump_18
      cases assump_17
      case intro assump_21 assump_22 =>
        apply False.elim assump_21
    let assump_16 := assump_11 assump_28
    apply False.elim assump_16


variable (p6 p0 p5 p4 p7 : Prop)
theorem file80_31407 : ((((((p4 → False) → False) ∨ ((p7 ∧ p0) → (p7 ∨ False))) ∧ (((p6 → False) ∨ (False → p7)) → False)) ∧ ((((False ∨ p0) ∧ (True → p4)) → ((p7 → p5) → (p7 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_62 : (((False ∨ p0) ∧ (True → p4)) → ((p7 → p5) → (p7 → p7))) := by
          intro assump_15
          intro assump_16
          intro assump_17
          cases assump_15
          case intro assump_22 assump_23 =>
            cases assump_22
            case inl assump_24 =>
              apply False.elim assump_24
            case inr assump_25 =>
              exact assump_17
        let assump_14 := assump_3 assump_62
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_63 : (((False ∨ p0) ∧ (True → p4)) → ((p7 → p5) → (p7 → p7))) := by
          intro assump_42
          intro assump_43
          intro assump_44
          cases assump_42
          case intro assump_49 assump_50 =>
            cases assump_49
            case inl assump_51 =>
              apply False.elim assump_51
            case inr assump_52 =>
              exact assump_44
        let assump_41 := assump_3 assump_63
        apply False.elim assump_41


variable (p7 p0 p6 p4 p3 p5 p1 : Prop)
theorem file80_32817 : ((((((True → p6) ∧ (p6 ∧ p7)) ∧ ((p6 → False) ∨ (p0 ∨ p7))) ∧ (((False ∧ p5) ∧ (p0 ∧ p1)) ∧ ((True ∧ False) → (p1 → p1)))) ∨ ((((False → False) ∧ (p7 ∨ p5)) ∧ ((p7 ∨ True) ∨ (p4 ∨ p3))) ∧ (((p7 → False) ∧ (False ∨ p1)) ∧ ((True ∧ True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_7
            case inl assump_18 =>
              cases assump_5
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_26
            case inr assump_19 =>
              cases assump_19
              case inl assump_30 =>
                cases assump_5
                case intro assump_34 assump_35 =>
                  cases assump_34
                  case intro assump_36 assump_37 =>
                    cases assump_36
                    case intro assump_38 assump_39 =>
                      apply False.elim assump_38
              case inr assump_31 =>
                cases assump_5
                case intro assump_44 assump_45 =>
                  cases assump_44
                  case intro assump_46 assump_47 =>
                    cases assump_46
                    case intro assump_48 assump_49 =>
                      apply False.elim assump_48
  case inr assump_3 =>
    cases assump_3
    case intro assump_52 assump_53 =>
      cases assump_52
      case intro assump_54 assump_55 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          cases assump_57
          case inl assump_60 =>
            cases assump_55
            case inl assump_64 =>
              cases assump_64
              case inl assump_66 =>
                cases assump_53
                case intro assump_70 assump_71 =>
                  cases assump_70
                  case intro assump_72 assump_73 =>
                    cases assump_73
                    case inl assump_76 =>
                      apply False.elim assump_76
                    case inr assump_77 =>
                      have assump_238 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_84 := assump_71 assump_238
                      apply False.elim assump_84
              case inr assump_67 =>
                cases assump_53
                case intro assump_90 assump_91 =>
                  cases assump_90
                  case intro assump_92 assump_93 =>
                    cases assump_93
                    case inl assump_96 =>
                      apply False.elim assump_96
                    case inr assump_97 =>
                      have assump_239 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_104 := assump_91 assump_239
                      apply False.elim assump_104
            case inr assump_65 =>
              cases assump_65
              case inl assump_108 =>
                cases assump_53
                case intro assump_112 assump_113 =>
                  cases assump_112
                  case intro assump_114 assump_115 =>
                    cases assump_115
                    case inl assump_118 =>
                      apply False.elim assump_118
                    case inr assump_119 =>
                      have assump_240 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_126 := assump_113 assump_240
                      apply False.elim assump_126
              case inr assump_109 =>
                cases assump_53
                case intro assump_132 assump_133 =>
                  cases assump_132
                  case intro assump_134 assump_135 =>
                    cases assump_135
                    case inl assump_138 =>
                      apply False.elim assump_138
                    case inr assump_139 =>
                      have assump_241 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_146 := assump_133 assump_241
                      apply False.elim assump_146
          case inr assump_61 =>
            cases assump_55
            case inl assump_152 =>
              cases assump_152
              case inl assump_154 =>
                cases assump_53
                case intro assump_158 assump_159 =>
                  cases assump_158
                  case intro assump_160 assump_161 =>
                    cases assump_161
                    case inl assump_164 =>
                      apply False.elim assump_164
                    case inr assump_165 =>
                      have assump_242 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_172 := assump_159 assump_242
                      apply False.elim assump_172
              case inr assump_155 =>
                cases assump_53
                case intro assump_178 assump_179 =>
                  cases assump_178
                  case intro assump_180 assump_181 =>
                    cases assump_181
                    case inl assump_184 =>
                      apply False.elim assump_184
                    case inr assump_185 =>
                      have assump_243 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_192 := assump_179 assump_243
                      apply False.elim assump_192
            case inr assump_153 =>
              cases assump_153
              case inl assump_196 =>
                cases assump_53
                case intro assump_200 assump_201 =>
                  cases assump_200
                  case intro assump_202 assump_203 =>
                    cases assump_203
                    case inl assump_206 =>
                      apply False.elim assump_206
                    case inr assump_207 =>
                      have assump_244 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_214 := assump_201 assump_244
                      apply False.elim assump_214
              case inr assump_197 =>
                cases assump_53
                case intro assump_220 assump_221 =>
                  cases assump_220
                  case intro assump_222 assump_223 =>
                    cases assump_223
                    case inl assump_226 =>
                      apply False.elim assump_226
                    case inr assump_227 =>
                      have assump_245 : (True ∧ True) := by
                        apply And.intro
                        apply True.intro
                        apply True.intro
                      let assump_234 := assump_221 assump_245
                      apply False.elim assump_234


variable (p0 p1 p2 p6 p4 p7 p3 p5 : Prop)
theorem file80_40556 : (((((p6 ∨ p4) ∨ (p6 ∧ False)) ∨ ((False ∧ p1) → (p0 ∧ True))) ∨ (((False → False) ∧ (p6 → p5)) ∨ ((p3 → False) → (p3 → False)))) ∨ ((((p5 ∧ p7) ∨ (True ∧ False)) ∨ ((p2 ∧ p7) ∧ (p6 ∨ p3))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  apply True.intro


variable (p0 p2 p6 p5 p7 : Prop)
theorem file80_40998 : ((((((p6 ∨ p5) ∨ (p0 ∨ p7)) ∨ ((p6 ∨ True) ∨ (False → False))) ∨ (((p0 → p2) → False) → False)) → False) → False) := by
  intro assump_12
  have assump_19 : ((((p6 ∨ p5) ∨ (p0 ∨ p7)) ∨ ((p6 ∨ True) ∨ (False → False))) ∨ (((p0 → p2) → False) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_15 := assump_12 assump_19
  apply False.elim assump_15


variable (p2 p1 p7 p4 p5 p0 : Prop)
theorem file80_41472 : (((((True ∧ p1) → False) → ((p4 ∨ p5) ∧ (p4 ∨ p2))) ∧ (((p7 ∧ p4) → False) ∧ ((p0 → False) → False))) → ((((p5 ∧ False) → (p5 ∧ p4)) ∧ ((False ∨ p5) ∨ (True ∨ p2))) ∨ (((p7 ∧ p2) → False) ∨ ((p7 → False) ∨ (True ∨ False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply And.intro
      intro assump_12
      apply And.intro
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
      cases assump_12
      case intro assump_19 assump_20 =>
        apply False.elim assump_20
      apply Or.inr
      apply Or.inl
      apply True.intro


variable (p7 p0 p1 p5 p4 p3 p6 : Prop)
theorem file80_42229 : (((((p6 ∧ p1) ∨ (p7 ∨ p3)) → ((True → False) → False)) ∨ (((p3 → False) ∨ (p5 → False)) → ((p1 ∨ p0) ∨ (p5 ∧ p3)))) ∧ ((((p6 ∨ True) ∧ (False → False)) ∨ ((p4 ∧ p6) → False)) → (((p4 → True) → False) → False))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_74 : True := by
        apply True.intro
      let assump_15 := assump_2 assump_74
      apply False.elim assump_15
  case inr assump_6 =>
    cases assump_6
    case inl assump_19 =>
      have assump_75 : True := by
        apply True.intro
      let assump_24 := assump_2 assump_75
      apply False.elim assump_24
    case inr assump_20 =>
      have assump_76 : True := by
        apply True.intro
      let assump_31 := assump_2 assump_76
      apply False.elim assump_31
  intro assump_35
  intro assump_36
  cases assump_35
  case inl assump_39 =>
    cases assump_39
    case intro assump_41 assump_42 =>
      cases assump_41
      case inl assump_43 =>
        have assump_77 : (p4 → True) := by
          intro assump_52
          apply True.intro
        let assump_51 := assump_36 assump_77
        apply False.elim assump_51
      case inr assump_44 =>
        have assump_78 : (p4 → True) := by
          intro assump_62
          apply True.intro
        let assump_61 := assump_36 assump_78
        apply False.elim assump_61
  case inr assump_40 =>
    have assump_79 : (p4 → True) := by
      intro assump_70
      apply True.intro
    let assump_69 := assump_36 assump_79
    apply False.elim assump_69


variable (p3 p2 p5 p4 p7 : Prop)
theorem file80_43907 : (((((p5 → True) → False) ∧ ((p7 → False) ∧ (p3 ∨ False))) → False) ∨ ((((True ∨ p7) ∨ (p4 ∧ True)) → ((p3 → False) ∧ (p4 ∨ p7))) ∨ (((True → False) ∨ (p2 ∧ p5)) ∧ ((True ∨ p2) → (p5 ∧ p2))))) := by
  apply Or.inl
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_15
    case intro assump_18 assump_19 =>
      cases assump_19
      case inl assump_22 =>
        have assump_35 : (p5 → True) := by
          intro assump_29
          apply True.intro
        let assump_28 := assump_14 assump_35
        apply False.elim assump_28
      case inr assump_23 =>
        apply False.elim assump_23


variable (p6 p7 p1 p4 p0 : Prop)
theorem file80_44596 : ((((((p4 ∧ p0) ∧ (p6 ∨ False)) ∧ ((p1 ∧ p0) → (False ∧ True))) → (((p6 → False) → (p6 → p4)) → ((p7 → p6) ∧ (p0 ∧ True)))) → False) → False) := by
  intro assump_5
  have assump_57 : ((((p4 ∧ p0) ∧ (p6 ∨ False)) ∧ ((p1 ∧ p0) → (False ∧ True))) → (((p6 → False) → (p6 → p4)) → ((p7 → p6) ∧ (p0 ∧ True)))) := by
    intro assump_9
    intro assump_10
    apply And.intro
    intro assump_11
    cases assump_9
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          cases assump_19
          case inl assump_26 =>
            exact assump_26
          case inr assump_27 =>
            apply False.elim assump_27
    apply And.intro
    cases assump_9
    case intro assump_36 assump_37 =>
      cases assump_36
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_39
          case inl assump_46 =>
            exact assump_41
          case inr assump_47 =>
            apply False.elim assump_47
    apply True.intro
  let assump_8 := assump_5 assump_57
  apply False.elim assump_8


variable (p0 p4 p3 p7 p1 p6 : Prop)
theorem file80_45835 : ((((((False ∨ p0) ∨ (True ∨ p1)) ∧ ((p1 ∧ p4) → (p3 → False))) → False) ∧ ((((p6 → True) ∨ (p7 → False)) ∨ ((p1 → p3) → False)) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_19 : (((p6 → True) ∨ (p7 → False)) ∨ ((p1 → p3) → False)) := by
      apply Or.inl
      apply Or.inl
      intro assump_15
      apply True.intro
    let assump_14 := assump_9 assump_19
    apply False.elim assump_14


variable (p0 p7 p5 p3 p2 p4 : Prop)
theorem file80_46350 : ((((((False → False) → (p7 ∨ p4)) ∨ ((False → False) → False)) ∨ (((p0 ∧ p0) ∨ (p2 → False)) → False)) ∧ ((((p5 → False) ∧ (p7 ∧ p3)) → ((False ∧ p4) → (p4 ∧ p0))) → False)) → False) := by
  intro assump_38
  cases assump_38
  case intro assump_39 assump_40 =>
    cases assump_39
    case inl assump_41 =>
      cases assump_41
      case inl assump_43 =>
        have assump_99 : (((p5 → False) ∧ (p7 ∧ p3)) → ((False ∧ p4) → (p4 ∧ p0))) := by
          intro assump_50
          intro assump_51
          apply And.intro
          cases assump_51
          case intro assump_52 assump_53 =>
            apply False.elim assump_52
          cases assump_51
          case intro assump_56 assump_57 =>
            apply False.elim assump_56
        let assump_49 := assump_40 assump_99
        apply False.elim assump_49
      case inr assump_44 =>
        have assump_100 : (((p5 → False) ∧ (p7 ∧ p3)) → ((False ∧ p4) → (p4 ∧ p0))) := by
          intro assump_68
          intro assump_69
          apply And.intro
          cases assump_69
          case intro assump_70 assump_71 =>
            apply False.elim assump_70
          cases assump_69
          case intro assump_74 assump_75 =>
            apply False.elim assump_74
        let assump_67 := assump_40 assump_100
        apply False.elim assump_67
    case inr assump_42 =>
      have assump_101 : (((p5 → False) ∧ (p7 ∧ p3)) → ((False ∧ p4) → (p4 ∧ p0))) := by
        intro assump_86
        intro assump_87
        apply And.intro
        cases assump_87
        case intro assump_88 assump_89 =>
          apply False.elim assump_88
        cases assump_87
        case intro assump_92 assump_93 =>
          apply False.elim assump_92
      let assump_85 := assump_40 assump_101
      apply False.elim assump_85


variable (p7 p1 p2 p3 p0 p4 : Prop)
theorem file80_48196 : (((((p0 ∨ True) → False) → False) → False) → ((((True ∨ p1) ∧ (p1 ∨ p7)) ∨ ((p4 ∨ True) → (p4 ∨ p7))) → (((p2 → False) ∨ (False ∧ p2)) ∨ ((False → p1) ∧ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case inl assump_11 =>
          apply Or.inl
          apply Or.inl
          intro assump_17
          have assump_112 : (((p0 ∨ True) → False) → False) := by
            intro assump_22
            have assump_113 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_25 := assump_22 assump_113
            apply False.elim assump_25
          let assump_21 := assump_1 assump_112
          apply False.elim assump_21
        case inr assump_12 =>
          apply Or.inl
          apply Or.inl
          intro assump_36
          have assump_114 : (((p0 ∨ True) → False) → False) := by
            intro assump_41
            have assump_115 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_44 := assump_41 assump_115
            apply False.elim assump_44
          let assump_40 := assump_1 assump_114
          apply False.elim assump_40
      case inr assump_8 =>
        cases assump_6
        case inl assump_53 =>
          apply Or.inl
          apply Or.inl
          intro assump_59
          have assump_116 : (((p0 ∨ True) → False) → False) := by
            intro assump_64
            have assump_117 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_67 := assump_64 assump_117
            apply False.elim assump_67
          let assump_63 := assump_1 assump_116
          apply False.elim assump_63
        case inr assump_54 =>
          apply Or.inl
          apply Or.inl
          intro assump_78
          have assump_118 : (((p0 ∨ True) → False) → False) := by
            intro assump_83
            have assump_119 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_86 := assump_83 assump_119
            apply False.elim assump_86
          let assump_82 := assump_1 assump_118
          apply False.elim assump_82
  case inr assump_4 =>
    apply Or.inl
    apply Or.inl
    intro assump_97
    have assump_120 : (((p0 ∨ True) → False) → False) := by
      intro assump_102
      have assump_121 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_105 := assump_102 assump_121
      apply False.elim assump_105
    let assump_101 := assump_1 assump_120
    apply False.elim assump_101


variable (p4 p2 p0 p6 p1 p3 p5 p7 : Prop)
theorem file80_50990 : (((((True → False) → (p2 ∧ p1)) → False) → (((p0 → p7) → (p2 ∨ p3)) ∨ ((p6 → False) → (False → False)))) ∨ ((((p4 ∨ False) → (p7 → False)) ∨ ((p2 → False) ∨ (p1 → p4))) → (((p6 → p6) ∨ (p5 → False)) ∧ ((True → p3) → (True ∨ p1))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_25 : ((True → False) → (p2 ∧ p1)) := by
    intro assump_9
    apply And.intro
    have assump_26 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_26
    apply False.elim assump_12
    have assump_27 : True := by
      apply True.intro
    let assump_18 := assump_9 assump_27
    apply False.elim assump_18
  let assump_8 := assump_1 assump_25
  apply False.elim assump_8


variable (p6 p7 p4 p1 p5 p0 p2 p3 : Prop)
theorem file80_51768 : (((((False ∧ p2) → (p5 → False)) ∨ ((p2 ∨ p6) ∧ (p4 → False))) ∧ (((p3 → False) ∧ (p6 → p1)) → ((p5 ∧ True) → (p5 ∧ True)))) ∨ ((((True ∧ p1) ∨ (p2 ∧ p7)) ∨ ((p5 ∧ p0) → (p3 → False))) ∨ (((p3 ∨ p4) ∧ (p5 → p7)) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  intro assump_9
  intro assump_10
  apply And.intro
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_9
    case intro assump_17 assump_18 =>
      exact assump_11
  apply True.intro


variable (p2 p0 p5 p1 p4 p7 p3 : Prop)
theorem file80_52428 : (((((p7 → False) ∧ (True → p0)) ∨ ((p7 → False) ∨ (p4 ∧ True))) → (((True ∧ True) → False) → ((p7 → p0) → (p0 → False)))) ∨ ((((False → False) → False) ∨ ((p4 ∧ p5) → (p5 → False))) → (((p2 → p3) ∧ (p7 → False)) ∨ ((p7 → p2) → (p3 → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case inl assump_11 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      have assump_46 : (True ∧ True) := by
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_22 := assump_2 assump_46
      apply False.elim assump_22
  case inr assump_12 =>
    cases assump_12
    case inl assump_26 =>
      have assump_47 : (True ∧ True) := by
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_31 := assump_2 assump_47
      apply False.elim assump_31
    case inr assump_27 =>
      cases assump_27
      case intro assump_35 assump_36 =>
        have assump_48 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_42 := assump_2 assump_48
        apply False.elim assump_42


variable (p5 p6 p3 p7 p1 p0 : Prop)
theorem file80_53663 : ((((((False ∧ p5) → (p3 → False)) → False) → (((p6 → p7) → False) ∧ ((p7 ∧ p0) ∧ (p1 ∨ p1)))) ∧ ((((p1 → False) → (True ∧ p3)) → ((False → False) ∨ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p1 → False) → (True ∧ p3)) → ((False → False) ∨ (p3 → False))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p3 p4 p2 p1 p5 p6 p7 p0 : Prop)
theorem file80_54242 : ((((((True → False) ∧ (p5 → False)) ∧ ((p2 ∧ p5) ∧ (p5 ∨ True))) → (((p6 → p3) ∨ (False → False)) ∨ ((False ∨ False) ∨ (p2 ∨ p0)))) → ((((p7 → True) → False) ∧ ((False ∧ p1) → False)) ∧ (((p5 ∧ p4) → (p5 → p5)) ∧ ((p2 → False) → (p6 → False))))) → False) := by
  intro assump_1
  have assump_56 : ((((True → False) ∧ (p5 → False)) ∧ ((p2 ∧ p5) ∧ (p5 ∨ True))) → (((p6 → p3) ∨ (False → False)) ∨ ((False ∨ False) ∨ (p2 ∨ p0)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case inl assump_22 =>
              apply Or.inl
              apply Or.inl
              intro assump_26
              have assump_57 : p5 := by
                exact assump_22
              let assump_33 := assump_9 assump_57
              apply False.elim assump_33
            case inr assump_23 =>
              apply Or.inl
              apply Or.inl
              intro assump_39
              have assump_58 : p5 := by
                exact assump_17
              let assump_45 := assump_9 assump_58
              apply False.elim assump_45
  let assump_4 := assump_1 assump_56
  let assump_49 := And.left assump_4
  let assump_50 := And.left assump_49
  have assump_59 : (p7 → True) := by
    intro assump_52
    apply True.intro
  let assump_51 := assump_50 assump_59
  apply False.elim assump_51


variable (p4 p1 p3 p0 p6 p2 p5 : Prop)
theorem file80_55854 : ((((((p5 → False) ∨ (p0 → False)) ∨ ((p4 → True) → (p5 → False))) ∧ (((p3 ∧ p5) ∧ (p2 ∨ p1)) → ((p5 → p0) ∨ (p2 ∧ True)))) ∧ ((((p1 → False) ∧ (False ∨ True)) ∧ ((p0 ∧ p0) ∨ (p0 → p5))) ∧ (((p6 ∧ p3) → (p2 → p2)) → False))) → False) := by
  intro assump_1
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
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_19
                case inl assump_22 =>
                  apply False.elim assump_22
                case inr assump_23 =>
                  cases assump_17
                  case inl assump_28 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      have assump_190 : ((p6 ∧ p3) → (p2 → p2)) := by
                        intro assump_39
                        intro assump_40
                        cases assump_39
                        case intro assump_43 assump_44 =>
                          exact assump_40
                      let assump_38 := assump_15 assump_190
                      apply False.elim assump_38
                  case inr assump_29 =>
                    have assump_191 : ((p6 ∧ p3) → (p2 → p2)) := by
                      intro assump_57
                      intro assump_58
                      cases assump_57
                      case intro assump_61 assump_62 =>
                        exact assump_58
                    let assump_56 := assump_15 assump_191
                    apply False.elim assump_56
        case inr assump_9 =>
          cases assump_3
          case intro assump_74 assump_75 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              cases assump_76
              case intro assump_78 assump_79 =>
                cases assump_79
                case inl assump_82 =>
                  apply False.elim assump_82
                case inr assump_83 =>
                  cases assump_77
                  case inl assump_88 =>
                    cases assump_88
                    case intro assump_90 assump_91 =>
                      have assump_192 : ((p6 ∧ p3) → (p2 → p2)) := by
                        intro assump_99
                        intro assump_100
                        cases assump_99
                        case intro assump_103 assump_104 =>
                          exact assump_100
                      let assump_98 := assump_75 assump_192
                      apply False.elim assump_98
                  case inr assump_89 =>
                    have assump_193 : ((p6 ∧ p3) → (p2 → p2)) := by
                      intro assump_117
                      intro assump_118
                      cases assump_117
                      case intro assump_121 assump_122 =>
                        exact assump_118
                    let assump_116 := assump_75 assump_193
                    apply False.elim assump_116
      case inr assump_7 =>
        cases assump_3
        case intro assump_134 assump_135 =>
          cases assump_134
          case intro assump_136 assump_137 =>
            cases assump_136
            case intro assump_138 assump_139 =>
              cases assump_139
              case inl assump_142 =>
                apply False.elim assump_142
              case inr assump_143 =>
                cases assump_137
                case inl assump_148 =>
                  cases assump_148
                  case intro assump_150 assump_151 =>
                    have assump_194 : ((p6 ∧ p3) → (p2 → p2)) := by
                      intro assump_159
                      intro assump_160
                      cases assump_159
                      case intro assump_163 assump_164 =>
                        exact assump_160
                    let assump_158 := assump_135 assump_194
                    apply False.elim assump_158
                case inr assump_149 =>
                  have assump_195 : ((p6 ∧ p3) → (p2 → p2)) := by
                    intro assump_177
                    intro assump_178
                    cases assump_177
                    case intro assump_181 assump_182 =>
                      exact assump_178
                  let assump_176 := assump_135 assump_195
                  apply False.elim assump_176


variable (p6 p2 p7 p3 p0 p1 p5 p4 : Prop)
theorem file80_60504 : ((((((p4 → p3) → False) → ((p7 ∧ p2) ∧ (p3 → False))) ∧ (((p3 → False) ∧ (p4 → p6)) ∧ ((p5 → False) → False))) ∧ ((((False ∧ p1) ∨ (p3 ∨ p5)) ∨ ((p0 ∧ p6) ∧ (True ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_33 : (p5 → False) := by
            intro assump_22
            have assump_34 : (((False ∧ p1) ∨ (p3 ∨ p5)) ∨ ((p0 ∧ p6) ∧ (True ∨ p7))) := by
              apply Or.inl
              apply Or.inr
              apply Or.inr
              exact assump_22
            let assump_26 := assump_3 assump_34
            apply False.elim assump_26
          let assump_21 := assump_9 assump_33
          apply False.elim assump_21


variable (p7 p6 p5 p4 p1 p2 p3 : Prop)
theorem file80_61457 : (((((p4 ∨ p4) ∧ (p1 → False)) ∧ ((p7 → False) → (p5 → False))) ∧ (((p2 ∧ True) → False) ∨ ((p3 ∨ p4) → (p1 → True)))) → ((((p6 → False) → False) → ((False ∧ False) → False)) ∧ (((False → p7) ∧ (p3 → False)) → ((p4 → False) → (True ∨ p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  intro assump_8
  intro assump_9
  cases assump_8
  case intro assump_12 assump_13 =>
    cases assump_1
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_22
          case inl assump_24 =>
            cases assump_19
            case inl assump_32 =>
              apply Or.inl
              apply True.intro
            case inr assump_33 =>
              apply Or.inl
              apply True.intro
          case inr assump_25 =>
            cases assump_19
            case inl assump_44 =>
              apply Or.inl
              apply True.intro
            case inr assump_45 =>
              apply Or.inl
              apply True.intro


variable (p1 p6 p3 p5 p4 p2 : Prop)
theorem file80_62700 : ((((((p4 → False) ∨ (p5 ∨ p5)) → ((p1 ∨ True) ∧ (p4 ∨ p3))) ∧ (((p4 ∧ True) → (p6 ∨ p3)) ∧ ((False → p6) → False))) ∨ ((((True ∧ True) ∧ (p3 ∨ False)) ∨ ((p2 → False) → (False → False))) → (((p3 → p5) → (p6 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_35 : (False → p6) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_9 assump_35
        apply False.elim assump_14
  case inr assump_3 =>
    have assump_36 : (((True ∧ True) ∧ (p3 ∨ False)) ∨ ((p2 → False) → (False → False))) := by
      apply Or.inr
      intro assump_24
      intro assump_25
      apply False.elim assump_25
    let assump_23 := assump_3 assump_36
    have assump_37 : ((p3 → p5) → (p6 ∨ True)) := by
      intro assump_29
      apply Or.inr
      apply True.intro
    let assump_28 := assump_23 assump_37
    apply False.elim assump_28


variable (p1 p5 p6 p4 p2 p7 p0 : Prop)
theorem file80_63805 : ((((((p0 → p1) ∨ (p6 ∧ p6)) ∨ ((p5 ∧ False) ∨ (p1 → False))) → (((True → p5) ∧ (False → p0)) ∨ ((p7 ∧ p7) → False))) ∧ ((((p7 → p4) ∧ (p2 → False)) → ((True ∨ False) ∨ (p2 ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p7 → p4) ∧ (p2 → False)) → ((True ∨ False) ∨ (p2 ∨ False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p0 p1 p7 p4 p3 p2 : Prop)
theorem file80_64449 : (((((False ∨ p2) ∨ (p2 → False)) → False) → (((p4 → p0) ∧ (p2 ∨ p4)) ∨ ((p2 ∧ True) → False))) ∨ ((((p3 → False) ∧ (p1 ∨ True)) → ((p0 → p3) ∨ (False ∨ p7))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    have assump_33 : ((False ∨ p2) ∨ (p2 → False)) := by
      apply Or.inl
      apply Or.inr
      exact assump_22
    let assump_29 := assump_1 assump_33
    apply False.elim assump_29


variable (p2 p1 p0 p7 p5 p4 p3 : Prop)
theorem file80_64993 : (((((True → False) ∧ (p0 → False)) → False) → False) → ((((p7 ∨ p4) ∧ (False ∨ p0)) → ((p7 → False) ∨ (p3 → p4))) ∨ (((p5 → False) → (p2 ∨ p1)) ∨ ((p0 ∧ p5) ∨ (p7 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        apply Or.inl
        intro assump_17
        have assump_67 : (((True → False) ∧ (p0 → False)) → False) := by
          intro assump_24
          cases assump_24
          case intro assump_25 assump_26 =>
            have assump_68 : p0 := by
              exact assump_12
            let assump_31 := assump_26 assump_68
            apply False.elim assump_31
        let assump_23 := assump_1 assump_67
        apply False.elim assump_23
    case inr assump_8 =>
      cases assump_6
      case inl assump_40 =>
        apply False.elim assump_40
      case inr assump_41 =>
        apply Or.inl
        intro assump_46
        have assump_69 : (((True → False) ∧ (p0 → False)) → False) := by
          intro assump_53
          cases assump_53
          case intro assump_54 assump_55 =>
            have assump_70 : p0 := by
              exact assump_41
            let assump_60 := assump_55 assump_70
            apply False.elim assump_60
        let assump_52 := assump_1 assump_69
        apply False.elim assump_52


variable (p1 p4 p7 p3 p5 p2 p6 : Prop)
theorem file80_66526 : (((((p4 ∧ True) → False) ∧ ((False ∧ p6) ∧ (p2 ∨ True))) → (((p4 ∨ True) ∨ (p6 → p2)) → False)) ∨ ((((p5 → p1) ∨ (p6 ∨ p4)) → ((p7 → False) ∧ (p2 ∧ p3))) ∨ (((p1 → False) → (p6 ∧ p1)) ∧ ((p4 → False) → (p4 ∧ False))))) := by
  apply Or.inl
  intro assump_17
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    cases assump_19
    case inl assump_21 =>
      cases assump_17
      case intro assump_25 assump_26 =>
        cases assump_26
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            apply False.elim assump_31
    case inr assump_22 =>
      cases assump_17
      case intro assump_37 assump_38 =>
        cases assump_38
        case intro assump_41 assump_42 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            apply False.elim assump_43
  case inr assump_20 =>
    cases assump_17
    case intro assump_49 assump_50 =>
      cases assump_50
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          apply False.elim assump_55


variable (p5 p4 p7 p2 : Prop)
theorem file80_67691 : (((((p4 → False) ∧ (p4 ∧ p5)) → ((p7 ∨ p5) ∨ (False ∧ p2))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p4 → False) ∧ (p4 ∧ p5)) → ((p7 ∨ p5) ∨ (False ∧ p2))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inr
        exact assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p0 p7 p2 p3 p6 : Prop)
theorem file80_68201 : (((((p3 → False) → (p7 → p2)) → ((p6 ∧ p7) ∨ (p7 → p2))) ∧ (((p0 ∨ p0) → False) ∧ ((p5 → False) ∧ (False ∨ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply False.elim assump_15


variable (p1 p6 p3 p5 p0 : Prop)
theorem file80_68732 : ((((((False → False) ∨ (p3 ∧ p5)) → ((False → False) ∧ (True → False))) → (((p3 → False) → (p1 → False)) ∨ ((p1 ∧ False) ∧ (p0 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((False → False) ∨ (p3 ∧ p5)) → ((False → False) ∧ (True → False))) → (((p3 → False) → (p1 → False)) ∨ ((p1 ∧ False) ∧ (p0 ∨ p6)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_30 : ((False → False) ∨ (p3 ∧ p5)) := by
      apply Or.inl
      intro assump_17
      apply False.elim assump_17
    let assump_16 := assump_5 assump_30
    let assump_20 := And.right assump_16
    have assump_31 : True := by
      apply True.intro
    let assump_22 := assump_20 assump_31
    apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p4 p7 p3 p6 p5 p0 : Prop)
theorem file80_69609 : (((((p0 ∨ p0) → (p2 ∨ p2)) ∨ ((p0 → p3) ∨ (p6 ∧ True))) ∧ (((False → p6) → False) ∧ ((p7 → False) ∨ (True → p4)))) → ((((p7 → p7) → (p0 → False)) ∨ ((True ∨ p0) ∨ (p4 ∧ p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_14
          case inl assump_17 =>
            have assump_409 : (False → p6) := by
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_13 assump_409
            apply False.elim assump_22
          case inr assump_18 =>
            have assump_410 : (False → p6) := by
              intro assump_34
              apply False.elim assump_34
            let assump_33 := assump_13 assump_410
            apply False.elim assump_33
      case inr assump_10 =>
        cases assump_10
        case inl assump_40 =>
          cases assump_8
          case intro assump_44 assump_45 =>
            cases assump_45
            case inl assump_48 =>
              have assump_411 : (False → p6) := by
                intro assump_54
                apply False.elim assump_54
              let assump_53 := assump_44 assump_411
              apply False.elim assump_53
            case inr assump_49 =>
              have assump_412 : (False → p6) := by
                intro assump_65
                apply False.elim assump_65
              let assump_64 := assump_44 assump_412
              apply False.elim assump_64
        case inr assump_41 =>
          cases assump_41
          case intro assump_71 assump_72 =>
            cases assump_8
            case intro assump_77 assump_78 =>
              cases assump_78
              case inl assump_81 =>
                have assump_413 : (False → p6) := by
                  intro assump_87
                  apply False.elim assump_87
                let assump_86 := assump_77 assump_413
                apply False.elim assump_86
              case inr assump_82 =>
                have assump_414 : (False → p6) := by
                  intro assump_98
                  apply False.elim assump_98
                let assump_97 := assump_77 assump_414
                apply False.elim assump_97
  case inr assump_4 =>
    cases assump_4
    case inl assump_104 =>
      cases assump_104
      case inl assump_106 =>
        cases assump_1
        case intro assump_110 assump_111 =>
          cases assump_110
          case inl assump_112 =>
            cases assump_111
            case intro assump_116 assump_117 =>
              cases assump_117
              case inl assump_120 =>
                have assump_415 : (False → p6) := by
                  intro assump_126
                  apply False.elim assump_126
                let assump_125 := assump_116 assump_415
                apply False.elim assump_125
              case inr assump_121 =>
                have assump_416 : (False → p6) := by
                  intro assump_137
                  apply False.elim assump_137
                let assump_136 := assump_116 assump_416
                apply False.elim assump_136
          case inr assump_113 =>
            cases assump_113
            case inl assump_143 =>
              cases assump_111
              case intro assump_147 assump_148 =>
                cases assump_148
                case inl assump_151 =>
                  have assump_417 : (False → p6) := by
                    intro assump_157
                    apply False.elim assump_157
                  let assump_156 := assump_147 assump_417
                  apply False.elim assump_156
                case inr assump_152 =>
                  have assump_418 : (False → p6) := by
                    intro assump_168
                    apply False.elim assump_168
                  let assump_167 := assump_147 assump_418
                  apply False.elim assump_167
            case inr assump_144 =>
              cases assump_144
              case intro assump_174 assump_175 =>
                cases assump_111
                case intro assump_180 assump_181 =>
                  cases assump_181
                  case inl assump_184 =>
                    have assump_419 : (False → p6) := by
                      intro assump_190
                      apply False.elim assump_190
                    let assump_189 := assump_180 assump_419
                    apply False.elim assump_189
                  case inr assump_185 =>
                    have assump_420 : (False → p6) := by
                      intro assump_201
                      apply False.elim assump_201
                    let assump_200 := assump_180 assump_420
                    apply False.elim assump_200
      case inr assump_107 =>
        cases assump_1
        case intro assump_209 assump_210 =>
          cases assump_209
          case inl assump_211 =>
            cases assump_210
            case intro assump_215 assump_216 =>
              cases assump_216
              case inl assump_219 =>
                have assump_421 : (False → p6) := by
                  intro assump_225
                  apply False.elim assump_225
                let assump_224 := assump_215 assump_421
                apply False.elim assump_224
              case inr assump_220 =>
                have assump_422 : (False → p6) := by
                  intro assump_236
                  apply False.elim assump_236
                let assump_235 := assump_215 assump_422
                apply False.elim assump_235
          case inr assump_212 =>
            cases assump_212
            case inl assump_242 =>
              cases assump_210
              case intro assump_246 assump_247 =>
                cases assump_247
                case inl assump_250 =>
                  have assump_423 : (False → p6) := by
                    intro assump_256
                    apply False.elim assump_256
                  let assump_255 := assump_246 assump_423
                  apply False.elim assump_255
                case inr assump_251 =>
                  have assump_424 : (False → p6) := by
                    intro assump_267
                    apply False.elim assump_267
                  let assump_266 := assump_246 assump_424
                  apply False.elim assump_266
            case inr assump_243 =>
              cases assump_243
              case intro assump_273 assump_274 =>
                cases assump_210
                case intro assump_279 assump_280 =>
                  cases assump_280
                  case inl assump_283 =>
                    have assump_425 : (False → p6) := by
                      intro assump_289
                      apply False.elim assump_289
                    let assump_288 := assump_279 assump_425
                    apply False.elim assump_288
                  case inr assump_284 =>
                    have assump_426 : (False → p6) := by
                      intro assump_300
                      apply False.elim assump_300
                    let assump_299 := assump_279 assump_426
                    apply False.elim assump_299
    case inr assump_105 =>
      cases assump_105
      case intro assump_306 assump_307 =>
        cases assump_1
        case intro assump_312 assump_313 =>
          cases assump_312
          case inl assump_314 =>
            cases assump_313
            case intro assump_318 assump_319 =>
              cases assump_319
              case inl assump_322 =>
                have assump_427 : (False → p6) := by
                  intro assump_328
                  apply False.elim assump_328
                let assump_327 := assump_318 assump_427
                apply False.elim assump_327
              case inr assump_323 =>
                have assump_428 : (False → p6) := by
                  intro assump_339
                  apply False.elim assump_339
                let assump_338 := assump_318 assump_428
                apply False.elim assump_338
          case inr assump_315 =>
            cases assump_315
            case inl assump_345 =>
              cases assump_313
              case intro assump_349 assump_350 =>
                cases assump_350
                case inl assump_353 =>
                  have assump_429 : (False → p6) := by
                    intro assump_359
                    apply False.elim assump_359
                  let assump_358 := assump_349 assump_429
                  apply False.elim assump_358
                case inr assump_354 =>
                  have assump_430 : (False → p6) := by
                    intro assump_370
                    apply False.elim assump_370
                  let assump_369 := assump_349 assump_430
                  apply False.elim assump_369
            case inr assump_346 =>
              cases assump_346
              case intro assump_376 assump_377 =>
                cases assump_313
                case intro assump_382 assump_383 =>
                  cases assump_383
                  case inl assump_386 =>
                    have assump_431 : (False → p6) := by
                      intro assump_392
                      apply False.elim assump_392
                    let assump_391 := assump_382 assump_431
                    apply False.elim assump_391
                  case inr assump_387 =>
                    have assump_432 : (False → p6) := by
                      intro assump_403
                      apply False.elim assump_403
                    let assump_402 := assump_382 assump_432
                    apply False.elim assump_402


variable (p4 p1 p7 p2 p0 p5 : Prop)
theorem file80_79410 : (((((p2 ∨ p1) → (p5 → p2)) → ((p2 → p4) ∧ (p1 → p4))) ∧ (((True → False) → (p1 ∨ p0)) → False)) → ((((True → False) → (p2 → False)) → False) ∧ (((p0 ∧ p7) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_42 : ((True → False) → (p1 ∨ p0)) := by
      intro assump_12
      have assump_43 : True := by
        apply True.intro
      let assump_15 := assump_12 assump_43
      apply False.elim assump_15
    let assump_11 := assump_6 assump_42
    apply False.elim assump_11
  intro assump_22
  cases assump_1
  case intro assump_25 assump_26 =>
    have assump_44 : ((True → False) → (p1 ∨ p0)) := by
      intro assump_32
      have assump_45 : True := by
        apply True.intro
      let assump_35 := assump_32 assump_45
      apply False.elim assump_35
    let assump_31 := assump_26 assump_44
    apply False.elim assump_31


variable (p4 p2 p0 p6 p7 p1 p5 p3 : Prop)
theorem file80_80400 : (((((False ∧ p3) ∧ (True → False)) ∨ ((p1 ∨ p4) ∧ (p7 → False))) → (((p3 → p5) ∧ (p3 → False)) → ((p5 → p7) → (p7 ∧ p7)))) → ((((p5 ∧ p2) ∨ (p6 → False)) ∧ ((p4 → p7) ∨ (p3 → p5))) → (((p3 ∨ p5) ∧ (p1 ∧ p7)) → ((p0 ∧ False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p4 p2 p1 p3 p7 : Prop)
theorem file80_80848 : (((((p1 ∧ p2) → False) ∧ ((p2 → True) → False)) → (((p4 → p7) ∧ (p3 ∧ True)) → False)) ∨ ((((p2 → False) ∧ (p3 → True)) → False) ∨ (((p4 → p3) → (True ∧ p1)) → ((p3 → False) → (p4 ∨ p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        have assump_24 : (p2 → True) := by
          intro assump_20
          apply True.intro
        let assump_19 := assump_14 assump_24
        apply False.elim assump_19


variable (p7 p5 p1 p0 p4 p2 p3 : Prop)
theorem file80_81499 : ((((((False → True) ∨ (p1 → False)) → ((p1 ∧ p4) → (p0 ∧ p2))) → False) ∧ ((((p7 ∧ p5) ∧ (p5 → False)) ∨ ((p0 ∨ p7) ∧ (p3 ∨ p0))) ∧ (((p3 ∨ p3) ∨ (p5 ∨ p1)) → False))) → False) := by
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
            have assump_150 : ((p3 ∨ p3) ∨ (p5 ∨ p1)) := by
              apply Or.inr
              apply Or.inl
              exact assump_13
            let assump_22 := assump_7 assump_150
            apply False.elim assump_22
      case inr assump_9 =>
        cases assump_9
        case intro assump_26 assump_27 =>
          cases assump_26
          case inl assump_28 =>
            cases assump_27
            case inl assump_32 =>
              have assump_151 : ((p3 ∨ p3) ∨ (p5 ∨ p1)) := by
                apply Or.inl
                apply Or.inl
                exact assump_32
              let assump_38 := assump_7 assump_151
              apply False.elim assump_38
            case inr assump_33 =>
              have assump_152 : (((False → True) ∨ (p1 → False)) → ((p1 ∧ p4) → (p0 ∧ p2))) := by
                intro assump_50
                intro assump_51
                apply And.intro
                cases assump_51
                case intro assump_52 assump_53 =>
                  cases assump_50
                  case inl assump_58 =>
                    exact assump_33
                  case inr assump_59 =>
                    exact assump_33
                cases assump_51
                case intro assump_64 assump_65 =>
                  cases assump_50
                  case inl assump_70 =>
                    have assump_153 : ((p3 ∨ p3) ∨ (p5 ∨ p1)) := by
                      apply Or.inr
                      apply Or.inr
                      exact assump_64
                    let assump_77 := assump_7 assump_153
                    apply False.elim assump_77
                  case inr assump_71 =>
                    have assump_154 : p1 := by
                      exact assump_64
                    let assump_83 := assump_71 assump_154
                    apply False.elim assump_83
              let assump_49 := assump_2 assump_152
              apply False.elim assump_49
          case inr assump_29 =>
            cases assump_27
            case inl assump_92 =>
              have assump_155 : ((p3 ∨ p3) ∨ (p5 ∨ p1)) := by
                apply Or.inl
                apply Or.inl
                exact assump_92
              let assump_98 := assump_7 assump_155
              apply False.elim assump_98
            case inr assump_93 =>
              have assump_156 : (((False → True) ∨ (p1 → False)) → ((p1 ∧ p4) → (p0 ∧ p2))) := by
                intro assump_110
                intro assump_111
                apply And.intro
                cases assump_111
                case intro assump_112 assump_113 =>
                  cases assump_110
                  case inl assump_118 =>
                    exact assump_93
                  case inr assump_119 =>
                    exact assump_93
                cases assump_111
                case intro assump_124 assump_125 =>
                  cases assump_110
                  case inl assump_130 =>
                    have assump_157 : ((p3 ∨ p3) ∨ (p5 ∨ p1)) := by
                      apply Or.inr
                      apply Or.inr
                      exact assump_124
                    let assump_137 := assump_7 assump_157
                    apply False.elim assump_137
                  case inr assump_131 =>
                    have assump_158 : p1 := by
                      exact assump_124
                    let assump_143 := assump_131 assump_158
                    apply False.elim assump_143
              let assump_109 := assump_2 assump_156
              apply False.elim assump_109


variable (p7 p0 p2 : Prop)
theorem file80_85596 : ((((((p0 ∧ p2) ∧ (p0 → False)) ∧ ((p7 ∧ p7) ∧ (p0 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p0 ∧ p2) ∧ (p0 → False)) ∧ ((p7 ∧ p7) ∧ (p0 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              have assump_36 : p0 := by
                exact assump_10
              let assump_28 := assump_19 assump_36
              apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p7 p3 p1 p2 p4 p6 p0 : Prop)
theorem file80_86433 : (((((p2 ∧ p7) → False) → ((p1 → p1) ∨ (p0 → p2))) → False) → ((((p4 → False) ∧ (True → p4)) → ((False ∧ p3) → False)) → (((False ∧ p6) → (p0 ∨ p4)) ∨ ((True ∧ p3) ∧ (p7 ∧ False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p2 p0 p5 p3 p4 p7 p6 p1 : Prop)
theorem file80_86834 : ((((((p6 ∧ p2) → False) ∨ ((p6 ∧ p1) → (p3 → False))) ∧ (((p4 ∧ p3) ∧ (p7 ∧ True)) ∨ ((p7 ∧ True) ∧ (False ∨ p4)))) ∧ ((((p5 ∧ True) ∧ (p5 → False)) → ((p0 → True) → False)) → False)) → False) := by
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
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_13
              case intro assump_20 assump_21 =>
                have assump_168 : (((p5 ∧ True) ∧ (p5 → False)) → ((p0 → True) → False)) := by
                  intro assump_29
                  intro assump_30
                  cases assump_29
                  case intro assump_33 assump_34 =>
                    cases assump_33
                    case intro assump_35 assump_36 =>
                      have assump_169 : p5 := by
                        exact assump_35
                      let assump_43 := assump_34 assump_169
                      apply False.elim assump_43
                let assump_28 := assump_3 assump_168
                apply False.elim assump_28
        case inr assump_11 =>
          cases assump_11
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_51
              case inl assump_58 =>
                apply False.elim assump_58
              case inr assump_59 =>
                have assump_170 : (((p5 ∧ True) ∧ (p5 → False)) → ((p0 → True) → False)) := by
                  intro assump_67
                  intro assump_68
                  cases assump_67
                  case intro assump_71 assump_72 =>
                    cases assump_71
                    case intro assump_73 assump_74 =>
                      have assump_171 : p5 := by
                        exact assump_73
                      let assump_81 := assump_72 assump_171
                      apply False.elim assump_81
                let assump_66 := assump_3 assump_170
                apply False.elim assump_66
      case inr assump_7 =>
        cases assump_5
        case inl assump_90 =>
          cases assump_90
          case intro assump_92 assump_93 =>
            cases assump_92
            case intro assump_94 assump_95 =>
              cases assump_93
              case intro assump_100 assump_101 =>
                have assump_172 : (((p5 ∧ True) ∧ (p5 → False)) → ((p0 → True) → False)) := by
                  intro assump_109
                  intro assump_110
                  cases assump_109
                  case intro assump_113 assump_114 =>
                    cases assump_113
                    case intro assump_115 assump_116 =>
                      have assump_173 : p5 := by
                        exact assump_115
                      let assump_123 := assump_114 assump_173
                      apply False.elim assump_123
                let assump_108 := assump_3 assump_172
                apply False.elim assump_108
        case inr assump_91 =>
          cases assump_91
          case intro assump_130 assump_131 =>
            cases assump_130
            case intro assump_132 assump_133 =>
              cases assump_131
              case inl assump_138 =>
                apply False.elim assump_138
              case inr assump_139 =>
                have assump_174 : (((p5 ∧ True) ∧ (p5 → False)) → ((p0 → True) → False)) := by
                  intro assump_147
                  intro assump_148
                  cases assump_147
                  case intro assump_151 assump_152 =>
                    cases assump_151
                    case intro assump_153 assump_154 =>
                      have assump_175 : p5 := by
                        exact assump_153
                      let assump_161 := assump_152 assump_175
                      apply False.elim assump_161
                let assump_146 := assump_3 assump_174
                apply False.elim assump_146


variable (p7 p5 p0 p6 p4 p3 p1 : Prop)
theorem file80_91053 : (((((True ∨ p3) ∨ (p0 ∨ p0)) → False) ∧ (((p4 ∨ False) → False) ∨ ((p0 ∨ p7) → False))) → ((((p5 ∨ p4) → False) → ((p6 → False) → False)) ∨ (((p4 ∨ p0) ∧ (p1 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      have assump_38 : ((True ∨ p3) ∨ (p0 ∨ p0)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_19 := assump_2 assump_38
      apply False.elim assump_19
    case inr assump_7 =>
      apply Or.inl
      intro assump_25
      intro assump_26
      have assump_39 : ((True ∨ p3) ∨ (p0 ∨ p0)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_34 := assump_2 assump_39
      apply False.elim assump_34


variable (p3 p7 p4 p6 : Prop)
theorem file80_91949 : (((((p6 → True) ∨ (p3 → False)) → False) → (((True → False) ∧ (p7 ∨ p7)) → False)) ∨ ((((True ∧ p7) → False) → False) ∨ (((p3 ∨ p4) ∨ (p6 → False)) ∧ ((p4 → True) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      have assump_27 : ((p6 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_14
        apply True.intro
      let assump_13 := assump_1 assump_27
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_28 : ((p6 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_23
        apply True.intro
      let assump_22 := assump_1 assump_28
      apply False.elim assump_22


variable (p5 p1 p0 p2 p7 p6 p4 : Prop)
theorem file80_92768 : (((((p5 → False) → (False → False)) ∨ ((p1 ∧ p4) → False)) → (((p5 ∧ p7) ∧ (p5 ∧ p4)) ∧ ((False ∧ p4) ∨ (p6 ∨ False)))) → ((((p5 ∨ p0) ∨ (p6 → True)) ∨ ((False ∨ p5) ∨ (p1 → False))) → (((p2 ∨ p2) ∨ (p1 ∨ True)) ∨ ((p1 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        apply Or.inl
        apply Or.inr
        apply Or.inr
        apply True.intro
      case inr assump_8 =>
        apply Or.inl
        apply Or.inr
        apply Or.inr
        apply True.intro
    case inr assump_6 =>
      apply Or.inl
      apply Or.inr
      apply Or.inr
      apply True.intro
  case inr assump_4 =>
    cases assump_4
    case inl assump_21 =>
      cases assump_21
      case inl assump_23 =>
        apply False.elim assump_23
      case inr assump_24 =>
        apply Or.inl
        apply Or.inr
        apply Or.inr
        apply True.intro
    case inr assump_22 =>
      apply Or.inl
      apply Or.inr
      apply Or.inr
      apply True.intro


variable (p0 p4 p2 p3 : Prop)
theorem file80_93917 : (((((p4 ∨ p0) → False) → ((False → p2) ∨ (False → p3))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p4 ∨ p0) → False) → ((False → p2) ∨ (False → p3))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p3 p5 p7 p6 p2 p4 p0 : Prop)
theorem file80_94309 : (((((p7 → p7) → False) ∧ ((True → False) ∧ (p5 ∧ p6))) ∧ (((p7 → False) ∧ (p4 → False)) → False)) → ((((p1 → False) ∧ (p0 → False)) → ((p0 → p4) ∧ (p0 ∨ p6))) ∨ (((p1 ∧ p3) ∨ (p2 ∨ p0)) ∧ ((True ∧ p7) → False)))) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          apply Or.inl
          intro assump_27
          apply And.intro
          intro assump_28
          cases assump_27
          case intro assump_31 assump_32 =>
            have assump_47 : p0 := by
              exact assump_28
            let assump_37 := assump_32 assump_47
            apply False.elim assump_37
          cases assump_27
          case intro assump_41 assump_42 =>
            apply Or.inr
            exact assump_20


variable (p0 p6 p2 p7 p3 : Prop)
theorem file80_95289 : (((((False → True) ∨ (p2 → False)) ∨ ((p7 → p0) ∧ (p3 → p6))) → False) → False) := by
  intro assump_8
  have assump_16 : (((False → True) ∨ (p2 → False)) ∨ ((p7 → p0) ∧ (p3 → p6))) := by
    apply Or.inl
    apply Or.inl
    intro assump_12
    apply True.intro
  let assump_11 := assump_8 assump_16
  apply False.elim assump_11


variable (p1 p3 p4 : Prop)
theorem file80_95670 : (((((True ∨ p4) ∧ (True ∧ p4)) → ((True ∨ p1) ∧ (p3 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_49 : (((True ∨ p4) ∧ (True ∧ p4)) → ((True ∨ p1) ∧ (p3 ∨ True))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply True.intro
      case inr assump_9 =>
        cases assump_7
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply True.intro
    cases assump_5
    case intro assump_26 assump_27 =>
      cases assump_26
      case inl assump_28 =>
        cases assump_27
        case intro assump_32 assump_33 =>
          apply Or.inr
          apply True.intro
      case inr assump_29 =>
        cases assump_27
        case intro assump_40 assump_41 =>
          apply Or.inr
          apply True.intro
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p5 p6 p4 : Prop)
theorem file80_96740 : (((((False ∧ p6) → False) → False) → False) ∨ ((((p4 → p5) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ p6) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p1 p0 p6 p5 p3 p7 p2 p4 : Prop)
theorem file80_97150 : (((((p2 → False) ∧ (p6 → False)) ∧ ((p7 → False) → False)) → (((p6 ∨ p6) ∨ (p2 → False)) ∧ ((True → p0) ∨ (p4 → p4)))) → ((((p7 → False) → (False → False)) ∨ ((p5 ∨ p1) → False)) ∨ (((p7 ∧ False) ∨ (p4 → p3)) ∧ ((True → False) → (p5 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p6 p1 p2 p7 p0 p3 p5 : Prop)
theorem file80_97574 : (((((p3 ∧ False) ∧ (p6 → False)) ∧ ((p1 ∧ True) → (p5 ∨ p6))) → (((p3 ∧ p1) ∧ (p2 ∧ p3)) → False)) ∨ ((((p1 ∨ p1) → (True ∨ p2)) ∧ ((p3 → False) → (False ∧ p2))) → (((p0 ∨ p6) → (False → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              apply False.elim assump_22


variable (p6 p2 p1 p0 : Prop)
theorem file80_98303 : ((((((p6 → False) ∨ (True ∨ p2)) ∧ ((False ∨ True) → False)) → (((False → p0) → False) ∨ ((p1 ∧ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_51 : ((((p6 → False) ∨ (True ∨ p2)) ∧ ((False ∨ True) → False)) → (((False → p0) → False) ∨ ((p1 ∧ p2) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_14
        have assump_52 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_18 := assump_7 assump_52
        apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case inl assump_22 =>
          apply Or.inl
          intro assump_28
          have assump_53 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_32 := assump_7 assump_53
          apply False.elim assump_32
        case inr assump_23 =>
          apply Or.inl
          intro assump_40
          have assump_54 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_44 := assump_7 assump_54
          apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p4 p0 p2 p5 p3 p1 p7 : Prop)
theorem file80_99637 : (((((p1 ∨ p7) ∧ (p4 ∨ p7)) ∧ ((True ∨ p5) → False)) → (((p0 → False) ∧ (False → False)) → False)) ∨ ((((p2 → False) ∧ (p2 ∨ False)) ∨ ((True → False) → (p3 → p0))) ∨ (((p5 ∨ p7) ∨ (p0 ∧ False)) → False))) := by
  apply Or.inl
  intro assump_12
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_12
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_22
        case inl assump_24 =>
          cases assump_23
          case inl assump_28 =>
            have assump_66 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_34 := assump_21 assump_66
            apply False.elim assump_34
          case inr assump_29 =>
            have assump_67 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_42 := assump_21 assump_67
            apply False.elim assump_42
        case inr assump_25 =>
          cases assump_23
          case inl assump_48 =>
            have assump_68 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_54 := assump_21 assump_68
            apply False.elim assump_54
          case inr assump_49 =>
            have assump_69 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_62 := assump_21 assump_69
            apply False.elim assump_62


variable (p4 p5 p6 p3 p7 p1 p2 : Prop)
theorem file80_101172 : ((((((p2 → False) → (p7 ∧ p7)) ∨ ((p2 → False) ∧ (p2 ∨ p6))) ∧ (((p4 → p2) ∨ (p7 → False)) ∨ ((p1 → False) → (False ∧ p5)))) ∧ ((((p3 → p3) ∧ (True → p1)) ∧ ((False → False) → False)) ∧ (((p2 ∨ p1) → (p6 ∧ p4)) ∨ ((p3 ∧ p6) ∧ (p1 ∧ False))))) → False) := by
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
          case inl assump_12 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  cases assump_17
                  case inl assump_28 =>
                    have assump_401 : (False → False) := by
                      intro assump_34
                      apply False.elim assump_34
                    let assump_33 := assump_19 assump_401
                    apply False.elim assump_33
                  case inr assump_29 =>
                    cases assump_29
                    case intro assump_40 assump_41 =>
                      cases assump_40
                      case intro assump_42 assump_43 =>
                        cases assump_41
                        case intro assump_48 assump_49 =>
                          apply False.elim assump_49
          case inr assump_13 =>
            cases assump_3
            case intro assump_56 assump_57 =>
              cases assump_56
              case intro assump_58 assump_59 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  cases assump_57
                  case inl assump_68 =>
                    have assump_402 : (False → False) := by
                      intro assump_74
                      apply False.elim assump_74
                    let assump_73 := assump_59 assump_402
                    apply False.elim assump_73
                  case inr assump_69 =>
                    cases assump_69
                    case intro assump_80 assump_81 =>
                      cases assump_80
                      case intro assump_82 assump_83 =>
                        cases assump_81
                        case intro assump_88 assump_89 =>
                          apply False.elim assump_89
        case inr assump_11 =>
          cases assump_3
          case intro assump_96 assump_97 =>
            cases assump_96
            case intro assump_98 assump_99 =>
              cases assump_98
              case intro assump_100 assump_101 =>
                cases assump_97
                case inl assump_108 =>
                  have assump_403 : (False → False) := by
                    intro assump_114
                    apply False.elim assump_114
                  let assump_113 := assump_99 assump_403
                  apply False.elim assump_113
                case inr assump_109 =>
                  cases assump_109
                  case intro assump_120 assump_121 =>
                    cases assump_120
                    case intro assump_122 assump_123 =>
                      cases assump_121
                      case intro assump_128 assump_129 =>
                        apply False.elim assump_129
      case inr assump_7 =>
        cases assump_7
        case intro assump_134 assump_135 =>
          cases assump_135
          case inl assump_138 =>
            cases assump_5
            case inl assump_142 =>
              cases assump_142
              case inl assump_144 =>
                cases assump_3
                case intro assump_148 assump_149 =>
                  cases assump_148
                  case intro assump_150 assump_151 =>
                    cases assump_150
                    case intro assump_152 assump_153 =>
                      cases assump_149
                      case inl assump_160 =>
                        have assump_404 : (False → False) := by
                          intro assump_169
                          apply False.elim assump_169
                        let assump_168 := assump_151 assump_404
                        apply False.elim assump_168
                      case inr assump_161 =>
                        cases assump_161
                        case intro assump_175 assump_176 =>
                          cases assump_175
                          case intro assump_177 assump_178 =>
                            cases assump_176
                            case intro assump_183 assump_184 =>
                              apply False.elim assump_184
              case inr assump_145 =>
                cases assump_3
                case intro assump_191 assump_192 =>
                  cases assump_191
                  case intro assump_193 assump_194 =>
                    cases assump_193
                    case intro assump_195 assump_196 =>
                      cases assump_192
                      case inl assump_203 =>
                        have assump_405 : (False → False) := by
                          intro assump_212
                          apply False.elim assump_212
                        let assump_211 := assump_194 assump_405
                        apply False.elim assump_211
                      case inr assump_204 =>
                        cases assump_204
                        case intro assump_218 assump_219 =>
                          cases assump_218
                          case intro assump_220 assump_221 =>
                            cases assump_219
                            case intro assump_226 assump_227 =>
                              apply False.elim assump_227
            case inr assump_143 =>
              cases assump_3
              case intro assump_234 assump_235 =>
                cases assump_234
                case intro assump_236 assump_237 =>
                  cases assump_236
                  case intro assump_238 assump_239 =>
                    cases assump_235
                    case inl assump_246 =>
                      have assump_406 : (False → False) := by
                        intro assump_255
                        apply False.elim assump_255
                      let assump_254 := assump_237 assump_406
                      apply False.elim assump_254
                    case inr assump_247 =>
                      cases assump_247
                      case intro assump_261 assump_262 =>
                        cases assump_261
                        case intro assump_263 assump_264 =>
                          cases assump_262
                          case intro assump_269 assump_270 =>
                            apply False.elim assump_270
          case inr assump_139 =>
            cases assump_5
            case inl assump_277 =>
              cases assump_277
              case inl assump_279 =>
                cases assump_3
                case intro assump_283 assump_284 =>
                  cases assump_283
                  case intro assump_285 assump_286 =>
                    cases assump_285
                    case intro assump_287 assump_288 =>
                      cases assump_284
                      case inl assump_295 =>
                        have assump_407 : (False → False) := by
                          intro assump_301
                          apply False.elim assump_301
                        let assump_300 := assump_286 assump_407
                        apply False.elim assump_300
                      case inr assump_296 =>
                        cases assump_296
                        case intro assump_307 assump_308 =>
                          cases assump_307
                          case intro assump_309 assump_310 =>
                            cases assump_308
                            case intro assump_315 assump_316 =>
                              apply False.elim assump_316
              case inr assump_280 =>
                cases assump_3
                case intro assump_323 assump_324 =>
                  cases assump_323
                  case intro assump_325 assump_326 =>
                    cases assump_325
                    case intro assump_327 assump_328 =>
                      cases assump_324
                      case inl assump_335 =>
                        have assump_408 : (False → False) := by
                          intro assump_341
                          apply False.elim assump_341
                        let assump_340 := assump_326 assump_408
                        apply False.elim assump_340
                      case inr assump_336 =>
                        cases assump_336
                        case intro assump_347 assump_348 =>
                          cases assump_347
                          case intro assump_349 assump_350 =>
                            cases assump_348
                            case intro assump_355 assump_356 =>
                              apply False.elim assump_356
            case inr assump_278 =>
              cases assump_3
              case intro assump_363 assump_364 =>
                cases assump_363
                case intro assump_365 assump_366 =>
                  cases assump_365
                  case intro assump_367 assump_368 =>
                    cases assump_364
                    case inl assump_375 =>
                      have assump_409 : (False → False) := by
                        intro assump_381
                        apply False.elim assump_381
                      let assump_380 := assump_366 assump_409
                      apply False.elim assump_380
                    case inr assump_376 =>
                      cases assump_376
                      case intro assump_387 assump_388 =>
                        cases assump_387
                        case intro assump_389 assump_390 =>
                          cases assump_388
                          case intro assump_395 assump_396 =>
                            apply False.elim assump_396


variable (p0 p7 p1 p5 p6 : Prop)
theorem file80_111380 : (((((p1 ∧ p5) → False) ∨ ((True ∨ p0) ∧ (p7 → True))) → False) → ((((p0 ∨ p1) ∧ (p0 → False)) ∨ ((p7 ∨ True) ∨ (p0 ∨ p5))) ∨ (((False ∧ p6) ∨ (p6 → False)) ∨ ((p6 → True) → (p1 ∨ p7))))) := by
  intro assump_9
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p4 p1 p3 p0 : Prop)
theorem file80_111723 : ((((((False → False) → (p0 → p0)) → False) → (((p3 → p4) ∧ (p0 ∧ p1)) → False)) → False) → False) := by
  intro assump_23
  have assump_54 : ((((False → False) → (p0 → p0)) → False) → (((p3 → p4) ∧ (p0 ∧ p1)) → False)) := by
    intro assump_27
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        have assump_55 : ((False → False) → (p0 → p0)) := by
          intro assump_42
          intro assump_43
          exact assump_43
        let assump_41 := assump_27 assump_55
        apply False.elim assump_41
  let assump_26 := assump_23 assump_54
  apply False.elim assump_26


variable (p5 p2 p0 p3 p6 p4 p7 p1 : Prop)
theorem file80_112461 : ((((((True ∧ p3) ∨ (p3 → p4)) → ((p7 ∧ p2) → (False → p2))) → (((False ∧ p6) ∨ (p0 ∨ True)) ∨ ((True → p3) ∨ (p3 ∨ p3)))) ∧ ((((False ∨ p0) → (p3 ∧ p1)) ∧ ((p6 → False) → (p1 ∧ True))) ∧ (((p4 → False) ∧ (False ∨ False)) ∧ ((p5 ∧ p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              apply False.elim assump_20
            case inr assump_21 =>
              apply False.elim assump_21


variable (p5 p3 p6 p1 p4 p0 : Prop)
theorem file80_113277 : (((((p1 → True) → (p5 ∧ p5)) → ((p5 → False) → False)) → (((p6 ∧ p3) → (p1 → False)) → ((p4 ∧ False) → False))) ∨ ((((p6 → p0) → False) → False) ∨ (((p5 → False) ∨ (p3 → False)) → ((p0 ∨ p5) ∨ (p1 ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5


variable (p2 p5 p4 p7 p1 p0 p6 p3 : Prop)
theorem file80_113703 : (((((p2 ∨ p7) → (False → p1)) ∨ ((p1 → p1) → (p6 ∧ False))) ∨ (((p7 ∨ p7) → (False → p3)) ∧ ((True ∨ p7) ∨ (p5 → False)))) ∨ ((((True ∧ True) → (True → False)) → ((p0 ∨ p1) → (p4 ∨ p5))) ∧ (((p7 → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p7 p5 p4 p2 p6 p3 p1 : Prop)
theorem file80_114103 : (((((False → p7) ∧ (False → p4)) → False) ∨ (((p7 ∨ p6) → (False → False)) → False)) → ((((p2 ∨ p4) → False) ∨ ((p1 → p5) → False)) ∧ (((p3 ∧ False) → (True → False)) → False))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_89 : ((False → p7) ∧ (False → p4)) := by
        apply And.intro
        intro assump_13
        apply False.elim assump_13
        intro assump_16
        apply False.elim assump_16
      let assump_12 := assump_2 assump_89
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_90 : ((False → p7) ∧ (False → p4)) := by
        apply And.intro
        intro assump_26
        apply False.elim assump_26
        intro assump_29
        apply False.elim assump_29
      let assump_25 := assump_2 assump_90
      apply False.elim assump_25
  case inr assump_3 =>
    apply Or.inl
    intro assump_37
    cases assump_37
    case inl assump_38 =>
      have assump_91 : ((p7 ∨ p6) → (False → False)) := by
        intro assump_44
        intro assump_45
        apply False.elim assump_45
      let assump_43 := assump_3 assump_91
      apply False.elim assump_43
    case inr assump_39 =>
      have assump_92 : ((p7 ∨ p6) → (False → False)) := by
        intro assump_55
        intro assump_56
        apply False.elim assump_56
      let assump_54 := assump_3 assump_92
      apply False.elim assump_54
  intro assump_62
  cases assump_1
  case inl assump_65 =>
    have assump_93 : ((False → p7) ∧ (False → p4)) := by
      apply And.intro
      intro assump_70
      apply False.elim assump_70
      intro assump_73
      apply False.elim assump_73
    let assump_69 := assump_65 assump_93
    apply False.elim assump_69
  case inr assump_66 =>
    have assump_94 : ((p7 ∨ p6) → (False → False)) := by
      intro assump_82
      intro assump_83
      apply False.elim assump_83
    let assump_81 := assump_66 assump_94
    apply False.elim assump_81


variable (p4 p6 p7 p1 p3 p5 : Prop)
theorem file80_116195 : (((((True ∨ False) ∧ (p1 ∨ p6)) → False) → False) → ((((p3 → False) ∨ (True → False)) → False) → (((p5 → False) ∨ (p3 → p7)) → ((p4 ∧ False) → (p6 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p7 p1 p3 p0 p6 p4 p5 : Prop)
theorem file80_116590 : ((((((p1 → p0) → False) → ((p6 → p6) ∨ (p7 → False))) ∧ (((p3 → True) → False) → ((p4 ∨ p6) ∧ (p0 → p5)))) → False) → False) := by
  intro assump_9
  have assump_40 : ((((p1 → p0) → False) → ((p6 → p6) ∨ (p7 → False))) ∧ (((p3 → True) → False) → ((p4 ∨ p6) ∧ (p0 → p5)))) := by
    apply And.intro
    intro assump_13
    apply Or.inl
    intro assump_16
    exact assump_16
    intro assump_19
    apply And.intro
    have assump_41 : (p3 → True) := by
      intro assump_23
      apply True.intro
    let assump_22 := assump_19 assump_41
    apply False.elim assump_22
    intro assump_27
    have assump_42 : (p3 → True) := by
      intro assump_33
      apply True.intro
    let assump_32 := assump_19 assump_42
    apply False.elim assump_32
  let assump_12 := assump_9 assump_40
  apply False.elim assump_12


variable (p7 p0 p3 p4 p2 p6 : Prop)
theorem file80_117464 : (((((p6 ∨ p2) → False) → ((p3 → False) → (p3 → p7))) ∨ (((p6 → False) → (p4 → p6)) ∧ ((p2 ∧ p4) → False))) ∨ ((((False ∨ p3) ∧ (p7 → p7)) ∨ ((p2 → False) → (p0 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_15 : p3 := by
    exact assump_3
  let assump_11 := assump_2 assump_15
  apply False.elim assump_11


variable (p2 p0 p7 p1 p6 : Prop)
theorem file80_117903 : ((((((p7 → False) → (False → False)) → False) → (((p6 → False) ∨ (True ∧ p0)) ∧ ((p1 ∨ True) ∧ (p6 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p7 → False) → (False → False)) → False) → (((p6 → False) ∨ (True ∧ p0)) ∧ ((p1 ∨ True) ∧ (p6 ∨ p2)))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    have assump_36 : ((p7 → False) → (False → False)) := by
      intro assump_13
      intro assump_14
      apply False.elim assump_14
    let assump_12 := assump_5 assump_36
    apply False.elim assump_12
    apply And.intro
    apply Or.inr
    apply True.intro
    have assump_37 : ((p7 → False) → (False → False)) := by
      intro assump_25
      intro assump_26
      apply False.elim assump_26
    let assump_24 := assump_5 assump_37
    apply False.elim assump_24
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p5 p4 p2 p6 : Prop)
theorem file80_118851 : ((((((p4 ∧ p5) ∨ (p4 ∧ p6)) → ((p5 → p5) → False)) → (((p6 → p5) → (False → p4)) ∨ ((p5 ∨ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p4 ∧ p5) ∨ (p4 ∧ p6)) → ((p5 → p5) → False)) → (((p6 → p5) → (False → p4)) ∨ ((p5 ∨ p2) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p6 p5 p0 p4 p3 p7 : Prop)
theorem file80_119357 : (((((p7 → False) ∧ (False ∧ False)) → False) ∨ (((False ∧ p3) ∨ (p5 ∨ p7)) → False)) ∨ ((((p6 ∨ p5) → False) ∨ ((p4 ∨ True) ∧ (p5 ∨ p3))) ∨ (((p1 → p0) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6


variable (p3 p0 p6 p2 p1 p4 p5 p7 : Prop)
theorem file80_119786 : ((((((p0 ∧ p3) ∧ (p7 ∧ False)) ∧ ((p2 ∧ p3) → (p3 ∨ p1))) → (((p2 ∨ p6) ∨ (p7 → False)) ∧ ((p0 ∨ p7) ∧ (p5 → p4)))) → False) → False) := by
  intro assump_1
  have assump_60 : ((((p0 ∧ p3) ∧ (p7 ∧ False)) ∧ ((p2 ∧ p3) → (p3 ∨ p1))) → (((p2 ∨ p6) ∨ (p7 → False)) ∧ ((p0 ∨ p7) ∧ (p5 → p4)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
    apply And.intro
    cases assump_5
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_25
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
    intro assump_38
    cases assump_5
    case intro assump_41 assump_42 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          cases assump_44
          case intro assump_51 assump_52 =>
            apply False.elim assump_52
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p1 p3 p6 p0 p4 p5 p7 : Prop)
theorem file80_121164 : ((((((False → p3) ∧ (False ∧ True)) ∧ ((p0 ∨ p4) ∨ (p4 → p7))) ∨ (((p5 → p5) → False) → ((p1 ∧ p7) ∧ (p7 → p7)))) → ((((p0 → p0) → False) → ((p4 ∨ p5) ∨ (True ∨ p3))) → (((p1 → p4) → (True ∨ p6)) → False))) → False) := by
  intro assump_13
  have assump_55 : ((((False → p3) ∧ (False ∧ True)) ∧ ((p0 ∨ p4) ∨ (p4 → p7))) ∨ (((p5 → p5) → False) → ((p1 ∧ p7) ∧ (p7 → p7)))) := by
    apply Or.inr
    intro assump_20
    apply And.intro
    apply And.intro
    have assump_56 : (p5 → p5) := by
      intro assump_24
      exact assump_24
    let assump_23 := assump_20 assump_56
    apply False.elim assump_23
    have assump_57 : (p5 → p5) := by
      intro assump_33
      exact assump_33
    let assump_32 := assump_20 assump_57
    apply False.elim assump_32
    intro assump_39
    exact assump_39
  let assump_16 := assump_13 assump_55
  have assump_58 : (((p0 → p0) → False) → ((p4 ∨ p5) ∨ (True ∨ p3))) := by
    intro assump_45
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_44 := assump_16 assump_58
  have assump_59 : ((p1 → p4) → (True ∨ p6)) := by
    intro assump_49
    apply Or.inl
    apply True.intro
  let assump_48 := assump_44 assump_59
  apply False.elim assump_48


variable (p1 p4 p6 p0 p2 p5 p3 p7 : Prop)
theorem file80_122435 : (((((p5 → p7) ∧ (False ∨ p7)) → ((False ∧ p6) → False)) ∨ (((p3 ∧ p3) → False) → ((p6 ∨ p1) → (p3 → False)))) ∧ ((((False → False) → False) → ((p1 ∧ True) ∧ (False → False))) ∨ (((True → p2) ∨ (p4 → p0)) ∧ ((False → p2) ∨ (p0 → p1))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3
  apply Or.inl
  intro assump_7
  apply And.intro
  apply And.intro
  have assump_20 : (False → False) := by
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_7 assump_20
  apply False.elim assump_10
  apply True.intro
  intro assump_17
  apply False.elim assump_17


variable (p7 p3 p2 : Prop)
theorem file80_123169 : (((((p7 → True) → False) → False) → False) → ((((p2 ∧ False) → False) → False) ∧ (((True → False) → False) → ((p7 → p3) ∨ (p3 ∨ p3))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_40 : (((p7 → True) → False) → False) := by
    intro assump_8
    have assump_41 : (p7 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_8 assump_41
    apply False.elim assump_11
  let assump_7 := assump_1 assump_40
  apply False.elim assump_7
  intro assump_19
  apply Or.inl
  intro assump_24
  have assump_42 : (((p7 → True) → False) → False) := by
    intro assump_29
    have assump_43 : (p7 → True) := by
      intro assump_33
      apply True.intro
    let assump_32 := assump_29 assump_43
    apply False.elim assump_32
  let assump_28 := assump_1 assump_42
  apply False.elim assump_28


variable (p6 p3 p4 p0 p5 p1 p2 : Prop)
theorem file80_124073 : (((((p2 → True) → False) → ((p3 ∧ p4) ∧ (p1 → p5))) → False) → ((((True → False) ∧ (p0 → p2)) ∧ ((True → False) ∧ (p5 ∧ p6))) ∨ (((True → False) ∨ (True ∨ p6)) ∨ ((p3 ∧ p3) ∨ (p2 ∨ p0))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  apply Or.inl
  intro assump_101
  have assump_133 : (((p2 → True) → False) → ((p3 ∧ p4) ∧ (p1 → p5))) := by
    intro assump_105
    apply And.intro
    apply And.intro
    have assump_134 : (p2 → True) := by
      intro assump_109
      apply True.intro
    let assump_108 := assump_105 assump_134
    apply False.elim assump_108
    have assump_135 : (p2 → True) := by
      intro assump_116
      apply True.intro
    let assump_115 := assump_105 assump_135
    apply False.elim assump_115
    intro assump_120
    have assump_136 : (p2 → True) := by
      intro assump_126
      apply True.intro
    let assump_125 := assump_105 assump_136
    apply False.elim assump_125
  let assump_104 := assump_1 assump_133
  apply False.elim assump_104


variable (p5 p1 p7 p2 p3 p0 : Prop)
theorem file80_125123 : (((((False → False) ∧ (p5 ∨ p0)) ∨ ((False ∨ False) → False)) → False) → ((((False → p3) → (True → False)) ∨ ((p1 ∨ p2) → (p7 ∧ p1))) → False)) := by
  intro assump_17
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    have assump_57 : (((False → False) ∧ (p5 ∨ p0)) ∨ ((False ∨ False) → False)) := by
      apply Or.inr
      intro assump_29
      cases assump_29
      case inl assump_30 =>
        apply False.elim assump_30
      case inr assump_31 =>
        apply False.elim assump_31
    let assump_25 := assump_17 assump_57
    apply False.elim assump_25
  case inr assump_20 =>
    have assump_58 : (((False → False) ∧ (p5 ∨ p0)) ∨ ((False ∨ False) → False)) := by
      apply Or.inr
      intro assump_47
      cases assump_47
      case inl assump_48 =>
        apply False.elim assump_48
      case inr assump_49 =>
        apply False.elim assump_49
    let assump_43 := assump_17 assump_58
    apply False.elim assump_43


variable (p7 p0 p3 p1 p2 p4 : Prop)
theorem file80_126131 : (((((p1 → True) → False) ∧ ((p4 ∧ p4) ∧ (p2 ∧ p1))) ∧ (((p3 ∧ True) ∧ (p7 ∨ p0)) → ((p4 → False) ∧ (False ∧ p2)))) → False) := by
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
            have assump_34 : (p1 → True) := by
              intro assump_30
              apply True.intro
            let assump_29 := assump_4 assump_34
            apply False.elim assump_29


variable (p1 p6 p5 p7 p2 p0 p4 : Prop)
theorem file80_126835 : (((((p4 → p5) ∨ (p6 → p0)) → ((p6 ∨ True) ∨ (False ∨ p5))) ∧ (((p2 ∧ False) ∨ (True ∨ p1)) ∨ ((False ∧ p4) → (p7 → p5)))) ∨ ((((p7 ∨ False) ∧ (p7 ∧ False)) → False) → (((p1 → p0) ∨ (p1 → False)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p3 p7 p6 p1 p5 p2 p4 : Prop)
theorem file80_127397 : ((((((p1 ∧ False) ∧ (p2 → p7)) ∨ ((p1 ∧ p3) → False)) ∧ (((False ∧ p1) → (p1 → p5)) → False)) ∨ ((((True → False) → (p7 ∧ p1)) ∧ ((p3 ∨ p4) ∨ (p3 → p6))) → False)) → False) := by
  intro assump_17
  cases assump_17
  case inl assump_18 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            apply False.elim assump_27
      case inr assump_23 =>
        have assump_88 : ((False ∧ p1) → (p1 → p5)) := by
          intro assump_37
          intro assump_38
          cases assump_37
          case intro assump_41 assump_42 =>
            apply False.elim assump_41
        let assump_36 := assump_21 assump_88
        apply False.elim assump_36
  case inr assump_19 =>
    have assump_89 : (((True → False) → (p7 ∧ p1)) ∧ ((p3 ∨ p4) ∨ (p3 → p6))) := by
      apply And.intro
      intro assump_51
      apply And.intro
      have assump_90 : True := by
        apply True.intro
      let assump_54 := assump_51 assump_90
      apply False.elim assump_54
      have assump_91 : True := by
        apply True.intro
      let assump_60 := assump_51 assump_91
      apply False.elim assump_60
      apply Or.inr
      intro assump_64
      have assump_92 : (((True → False) → (p7 ∧ p1)) ∧ ((p3 ∨ p4) ∨ (p3 → p6))) := by
        apply And.intro
        intro assump_69
        apply And.intro
        have assump_93 : True := by
          apply True.intro
        let assump_72 := assump_69 assump_93
        apply False.elim assump_72
        have assump_94 : True := by
          apply True.intro
        let assump_78 := assump_69 assump_94
        apply False.elim assump_78
        apply Or.inl
        apply Or.inl
        exact assump_64
      let assump_68 := assump_19 assump_92
      apply False.elim assump_68
    let assump_50 := assump_19 assump_89
    apply False.elim assump_50


variable (p6 p4 p0 p5 p7 p2 : Prop)
theorem file80_129449 : (((((p5 ∨ p2) → False) → False) → (((p0 ∧ p6) ∧ (p2 → False)) → False)) → ((((p6 → False) ∨ (False ∨ False)) → ((p5 → False) → (p2 ∧ False))) → (((p2 ∨ p2) → (p7 ∨ p2)) ∨ ((p0 → p4) ∧ (p4 → False))))) := by
  intro assump_35
  intro assump_36
  apply Or.inl
  intro assump_41
  cases assump_41
  case inl assump_42 =>
    apply Or.inr
    exact assump_42
  case inr assump_43 =>
    apply Or.inr
    exact assump_43


variable (p6 p2 p1 p5 p7 p4 : Prop)
theorem file80_129925 : (((((False → False) → False) → False) ∨ (((False ∧ p2) → False) ∧ ((p6 → False) → (p4 ∨ p1)))) ∧ ((((p2 ∧ False) → False) → False) → (((False ∧ p5) ∧ (p7 → False)) ∨ ((p1 → p7) → (p4 ∧ p1))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_43 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4
  intro assump_11
  apply Or.inr
  intro assump_14
  apply And.intro
  have assump_44 : ((p2 ∧ False) → False) := by
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      apply False.elim assump_21
  let assump_18 := assump_11 assump_44
  apply False.elim assump_18
  have assump_45 : ((p2 ∧ False) → False) := by
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      apply False.elim assump_35
  let assump_32 := assump_11 assump_45
  apply False.elim assump_32


variable (p0 p3 p2 p4 p1 p6 p5 : Prop)
theorem file80_130915 : (((((p3 ∧ p1) → False) → ((True ∨ p1) ∧ (p1 ∧ p5))) ∧ (((p0 ∧ p6) ∧ (p5 → False)) ∧ ((p5 ∧ p5) → False))) → ((((True ∨ p5) ∧ (True ∧ p4)) ∨ ((True ∧ False) → False)) ∨ (((True → False) → (p5 ∧ True)) → ((p5 → p1) → (p2 ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          apply Or.inr
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            apply False.elim assump_22


