variable (p4 p0 p7 p1 p3 : Prop)
theorem file91_41 : (((((p1 ∨ p7) ∨ (p4 ∨ p0)) ∨ ((p4 ∧ p3) → False)) → False) → False) := by
  intro assump_5
  have assump_25 : (((p1 ∨ p7) ∨ (p4 ∨ p0)) ∨ ((p4 ∧ p3) → False)) := by
    apply Or.inr
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      have assump_26 : (((p1 ∨ p7) ∨ (p4 ∨ p0)) ∨ ((p4 ∧ p3) → False)) := by
        apply Or.inl
        apply Or.inr
        apply Or.inl
        exact assump_10
      let assump_18 := assump_5 assump_26
      apply False.elim assump_18
  let assump_8 := assump_5 assump_25
  apply False.elim assump_8


variable (p1 p0 p3 p4 p2 p6 p5 : Prop)
theorem file91_665 : (((((p2 ∧ False) ∧ (p2 → False)) ∧ ((p4 → p5) → (p2 ∧ True))) ∧ (((p4 ∧ True) ∧ (p6 → False)) ∧ ((p0 ∧ p1) → (p5 → p3)))) → False) := by
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


variable (p1 p5 p3 p6 p0 p4 p7 : Prop)
theorem file91_1146 : ((((((p6 ∨ p4) ∧ (p3 ∨ p7)) → False) → False) ∧ ((((True → False) ∧ (p4 → False)) ∧ ((False ∨ True) → (p1 → p3))) ∧ (((p5 ∨ p0) ∧ (p7 ∨ p7)) → ((p5 → False) → (p1 → False))))) → False) := by
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    cases assump_45
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          have assump_70 : True := by
            apply True.intro
          let assump_66 := assump_52 assump_70
          apply False.elim assump_66


variable (p3 p1 : Prop)
theorem file91_1794 : (((((p1 ∧ False) → False) ∨ ((p1 → False) ∨ (p3 ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p1 ∧ False) → False) ∨ ((p1 → False) ∨ (p3 ∨ p3))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 : Prop)
theorem file91_2203 : (((((p7 → False) ∧ (False ∧ p7)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p7 → False) ∧ (False ∧ p7)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p3 p6 p0 p5 p1 : Prop)
theorem file91_2646 : (((((p6 ∨ p0) → (p0 ∧ p5)) ∧ ((True → False) ∧ (p3 ∨ True))) ∨ (((p1 ∧ p6) ∧ (p5 → p3)) ∧ ((p1 → False) ∧ (p4 → p1)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_50 : True := by
            apply True.intro
          let assump_17 := assump_8 assump_50
          apply False.elim assump_17
        case inr assump_13 =>
          have assump_51 : True := by
            apply True.intro
          let assump_23 := assump_8 assump_51
          apply False.elim assump_23
  case inr assump_3 =>
    cases assump_3
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_28
          case intro assump_39 assump_40 =>
            have assump_52 : p1 := by
              exact assump_31
            let assump_46 := assump_39 assump_52
            apply False.elim assump_46


variable (p2 p6 p3 p5 p1 p4 : Prop)
theorem file91_3828 : ((((((True ∨ p1) → False) → ((p1 → False) → False)) → False) ∧ ((((p2 ∨ p4) ∧ (p1 → False)) ∧ ((p1 ∧ p6) ∨ (p5 → False))) ∨ (((p2 ∨ p4) ∨ (p1 ∨ p3)) ∧ ((False ∨ True) ∧ (p2 ∧ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_9
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_228 : p1 := by
                  exact assump_20
                let assump_28 := assump_11 assump_228
                apply False.elim assump_28
            case inr assump_19 =>
              have assump_229 : (((True ∨ p1) → False) → ((p1 → False) → False)) := by
                intro assump_38
                intro assump_39
                have assump_230 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_44 := assump_38 assump_230
                apply False.elim assump_44
              let assump_37 := assump_2 assump_229
              apply False.elim assump_37
          case inr assump_13 =>
            cases assump_9
            case inl assump_55 =>
              cases assump_55
              case intro assump_57 assump_58 =>
                have assump_231 : p1 := by
                  exact assump_57
                let assump_65 := assump_11 assump_231
                apply False.elim assump_65
            case inr assump_56 =>
              have assump_232 : (((True ∨ p1) → False) → ((p1 → False) → False)) := by
                intro assump_75
                intro assump_76
                have assump_233 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_81 := assump_75 assump_233
                apply False.elim assump_81
              let assump_74 := assump_2 assump_232
              apply False.elim assump_74
    case inr assump_7 =>
      cases assump_7
      case intro assump_88 assump_89 =>
        cases assump_88
        case inl assump_90 =>
          cases assump_90
          case inl assump_92 =>
            cases assump_89
            case intro assump_96 assump_97 =>
              cases assump_96
              case inl assump_98 =>
                apply False.elim assump_98
              case inr assump_99 =>
                cases assump_97
                case intro assump_104 assump_105 =>
                  have assump_234 : (((True ∨ p1) → False) → ((p1 → False) → False)) := by
                    intro assump_114
                    intro assump_115
                    have assump_235 : (True ∨ p1) := by
                      apply Or.inl
                      apply True.intro
                    let assump_120 := assump_114 assump_235
                    apply False.elim assump_120
                  let assump_113 := assump_2 assump_234
                  apply False.elim assump_113
          case inr assump_93 =>
            cases assump_89
            case intro assump_129 assump_130 =>
              cases assump_129
              case inl assump_131 =>
                apply False.elim assump_131
              case inr assump_132 =>
                cases assump_130
                case intro assump_137 assump_138 =>
                  have assump_236 : (((True ∨ p1) → False) → ((p1 → False) → False)) := by
                    intro assump_147
                    intro assump_148
                    have assump_237 : (True ∨ p1) := by
                      apply Or.inl
                      apply True.intro
                    let assump_153 := assump_147 assump_237
                    apply False.elim assump_153
                  let assump_146 := assump_2 assump_236
                  apply False.elim assump_146
        case inr assump_91 =>
          cases assump_91
          case inl assump_160 =>
            cases assump_89
            case intro assump_164 assump_165 =>
              cases assump_164
              case inl assump_166 =>
                apply False.elim assump_166
              case inr assump_167 =>
                cases assump_165
                case intro assump_172 assump_173 =>
                  have assump_238 : (((True ∨ p1) → False) → ((p1 → False) → False)) := by
                    intro assump_182
                    intro assump_183
                    have assump_239 : (True ∨ p1) := by
                      apply Or.inl
                      apply True.intro
                    let assump_188 := assump_182 assump_239
                    apply False.elim assump_188
                  let assump_181 := assump_2 assump_238
                  apply False.elim assump_181
          case inr assump_161 =>
            cases assump_89
            case intro assump_197 assump_198 =>
              cases assump_197
              case inl assump_199 =>
                apply False.elim assump_199
              case inr assump_200 =>
                cases assump_198
                case intro assump_205 assump_206 =>
                  have assump_240 : (((True ∨ p1) → False) → ((p1 → False) → False)) := by
                    intro assump_215
                    intro assump_216
                    have assump_241 : (True ∨ p1) := by
                      apply Or.inl
                      apply True.intro
                    let assump_221 := assump_215 assump_241
                    apply False.elim assump_221
                  let assump_214 := assump_2 assump_240
                  apply False.elim assump_214


variable (p1 p0 p7 p3 : Prop)
theorem file91_9621 : (((((p7 → p0) ∧ (p0 ∧ False)) → ((p7 ∨ p1) ∧ (False → p3))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p7 → p0) ∧ (p0 ∧ False)) → ((p7 ∨ p1) ∧ (False → p3))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    intro assump_16
    apply False.elim assump_16
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p1 p4 p0 p2 p7 p3 p5 : Prop)
theorem file91_10177 : (((((True → p0) ∧ (p4 ∧ True)) ∨ ((True → p2) → False)) → (((p3 → True) ∧ (True ∧ p6)) → ((True ∨ p1) ∨ (p5 → False)))) ∨ ((((p1 ∧ p4) ∧ (p2 → False)) ∧ ((True → False) → False)) ∨ (((p4 → False) ∧ (False → False)) → ((p1 → p7) ∨ (False → p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      case inr assump_14 =>
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p6 p1 p5 p0 p7 p3 p2 : Prop)
theorem file91_11007 : (((((p1 → p2) → False) → False) → (((True ∨ p2) ∨ (True → p5)) → ((True ∧ True) ∨ (p6 → False)))) ∨ ((((p3 ∨ p6) → (p7 ∧ p6)) → False) ∧ (((p0 ∧ p1) → False) → False))) := by
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    cases assump_9
    case inl assump_11 =>
      apply Or.inl
      apply And.intro
      apply True.intro
      apply True.intro
    case inr assump_12 =>
      apply Or.inl
      apply And.intro
      apply True.intro
      apply True.intro
  case inr assump_10 =>
    apply Or.inl
    apply And.intro
    apply True.intro
    apply True.intro


variable (p1 p4 p0 p5 : Prop)
theorem file91_11673 : ((((((p0 → False) → (p1 → False)) ∨ ((p5 ∧ p5) ∨ (p5 → False))) → (((True ∨ p5) ∨ (True ∨ p4)) ∨ ((p4 → False) ∨ (p4 ∧ p4)))) → False) → False) := by
  intro assump_14
  have assump_36 : ((((p0 → False) → (p1 → False)) ∨ ((p5 ∧ p5) ∨ (p5 → False))) → (((True ∨ p5) ∨ (True ∨ p4)) ∨ ((p4 → False) ∨ (p4 ∧ p4)))) := by
    intro assump_18
    cases assump_18
    case inl assump_19 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_20 =>
      cases assump_20
      case inl assump_23 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_24 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
  let assump_17 := assump_14 assump_36
  apply False.elim assump_17


variable (p3 p0 p7 p6 : Prop)
theorem file91_12612 : (((((False → False) ∨ (p3 → p6)) → False) ∨ (((p3 ∧ False) ∧ (p0 ∧ p6)) ∨ ((p7 ∧ p3) ∧ (True → False)))) → False) := by
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    have assump_45 : ((False → False) ∨ (p3 → p6)) := by
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_10 assump_45
    apply False.elim assump_14
  case inr assump_11 =>
    cases assump_11
    case inl assump_21 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
    case inr assump_22 =>
      cases assump_22
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          have assump_46 : True := by
            apply True.intro
          let assump_41 := assump_32 assump_46
          apply False.elim assump_41


variable (p2 p6 p3 p0 p7 p1 : Prop)
theorem file91_13593 : (((((p6 → False) → (p0 → p6)) → ((True → False) → False)) ∨ (((True → p3) → (p6 ∧ p6)) ∨ ((p0 → False) ∧ (p1 ∧ p2)))) → ((((True ∧ p0) ∧ (p0 → False)) → ((p7 ∧ False) → False)) ∨ (((p7 → False) ∨ (True ∧ p0)) ∨ ((False ∨ p7) → (False ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case inl assump_14 =>
      apply Or.inl
      intro assump_18
      intro assump_19
      cases assump_19
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
    case inr assump_15 =>
      cases assump_15
      case intro assump_26 assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          apply Or.inl
          intro assump_36
          intro assump_37
          cases assump_37
          case intro assump_38 assump_39 =>
            apply False.elim assump_39


variable (p3 p5 p4 p2 p6 p7 p0 p1 : Prop)
theorem file91_14674 : (((((p1 → False) ∨ (p6 → False)) ∧ ((p4 → True) ∨ (p4 → p1))) → (((p4 → False) → (False → False)) ∨ ((p2 ∨ p5) → False))) ∨ ((((p4 ∧ False) ∨ (p5 ∧ p3)) ∧ ((p7 ∨ p3) ∧ (p5 → p0))) → (((False ∨ p4) → (p4 ∨ False)) ∧ ((True ∨ p4) ∨ (p1 → p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        apply False.elim assump_13
      case inr assump_9 =>
        apply Or.inl
        intro assump_18
        intro assump_19
        apply False.elim assump_19
    case inr assump_5 =>
      cases assump_3
      case inl assump_24 =>
        apply Or.inl
        intro assump_28
        intro assump_29
        apply False.elim assump_29
      case inr assump_25 =>
        apply Or.inl
        intro assump_34
        intro assump_35
        apply False.elim assump_35


variable (p7 p2 : Prop)
theorem file91_15692 : (((((True → False) → False) → ((True ∨ p2) → False)) → False) ∨ ((((p2 → False) ∧ (False → False)) ∧ ((p7 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_5
  have assump_20 : ((True → False) → False) := by
    intro assump_9
    have assump_21 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_21
    apply False.elim assump_12
  let assump_8 := assump_5 assump_20
  have assump_22 : (True ∨ p2) := by
    apply Or.inl
    apply True.intro
  let assump_16 := assump_8 assump_22
  apply False.elim assump_16


variable (p1 p0 p3 p6 p2 p5 : Prop)
theorem file91_16299 : ((((((p0 → p5) ∨ (True → False)) → False) ∧ (((p6 ∧ p5) ∧ (True → False)) → False)) ∧ ((((p2 → True) → False) → ((p3 → False) ∨ (p1 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_28 : (((p2 → True) → False) → ((p3 → False) ∨ (p1 → False))) := by
        intro assump_13
        apply Or.inl
        intro assump_16
        have assump_29 : (p2 → True) := by
          intro assump_21
          apply True.intro
        let assump_20 := assump_13 assump_29
        apply False.elim assump_20
      let assump_12 := assump_3 assump_28
      apply False.elim assump_12


variable (p2 p1 p7 p4 : Prop)
theorem file91_17049 : ((((((p1 → False) → False) → False) → False) ∧ ((((True ∨ p4) → (p7 ∧ p2)) → ((p2 → p2) ∧ (p2 ∧ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_29 : (((True ∨ p4) → (p7 ∧ p2)) → ((p2 → p2) ∧ (p2 ∧ p7))) := by
      intro assump_9
      apply And.intro
      intro assump_10
      exact assump_10
      apply And.intro
      have assump_30 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_17 := assump_9 assump_30
      let assump_18 := And.right assump_17
      exact assump_18
      have assump_31 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_23 := assump_9 assump_31
      let assump_24 := And.left assump_23
      exact assump_24
    let assump_8 := assump_3 assump_29
    apply False.elim assump_8


variable (p2 p1 p3 p0 p7 p6 : Prop)
theorem file91_17950 : ((((((p7 → False) ∧ (False ∧ p3)) ∧ ((p6 ∨ p1) ∨ (False → p2))) → (((p0 → False) → (False → False)) ∨ ((True ∨ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 → False) ∧ (False ∧ p3)) ∧ ((p6 ∨ p1) ∨ (False → p2))) → (((p0 → False) → (False → False)) ∨ ((True ∨ p1) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p0 p7 p5 p2 p1 : Prop)
theorem file91_18626 : (((((True → False) ∧ (p2 ∨ p5)) → ((p0 → p7) → False)) → False) → ((((p1 ∨ p3) ∨ (p7 ∨ p3)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_35 : (((True → False) ∧ (p2 ∨ p5)) → ((p0 → p7) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        have assump_36 : True := by
          apply True.intro
        let assump_21 := assump_12 assump_36
        apply False.elim assump_21
      case inr assump_17 =>
        have assump_37 : True := by
          apply True.intro
        let assump_28 := assump_12 assump_37
        apply False.elim assump_28
  let assump_7 := assump_1 assump_35
  apply False.elim assump_7


variable (p7 p5 p0 p6 : Prop)
theorem file91_19433 : ((((((False → True) → False) → ((p7 → p0) → (p5 → False))) ∨ (((False → False) ∧ (False → False)) ∨ ((p5 → True) ∨ (p5 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False → True) → False) → ((p7 → p0) → (p5 → False))) ∨ (((False → False) ∧ (False → False)) ∨ ((p5 → True) ∨ (p5 ∧ p6)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_23 : (False → True) := by
      intro assump_15
      apply True.intro
    let assump_14 := assump_5 assump_23
    apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p4 p6 p7 p5 p3 : Prop)
theorem file91_20110 : (((((p3 ∨ p2) ∨ (True → False)) → ((p4 ∧ p7) → False)) ∧ (((p3 ∨ p4) → False) ∨ ((p3 ∨ True) ∧ (p3 → False)))) → ((((p6 ∧ False) ∧ (p2 ∨ p3)) ∨ ((p6 ∨ True) ∨ (True → False))) ∨ (((True ∧ p4) → (p4 → p5)) ∨ ((p7 ∨ p2) → (False ∧ p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_13 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply Or.inr
          apply True.intro


variable (p1 p3 p4 p2 p5 p7 : Prop)
theorem file91_21032 : (((((p5 → False) → (p7 → False)) ∧ ((p1 ∧ p3) ∧ (False ∧ p2))) ∨ (((p1 → False) ∧ (p7 → p7)) ∧ ((p4 ∧ p7) ∧ (p4 → False)))) → False) := by
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
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
  case inr assump_3 =>
    cases assump_3
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_21
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            have assump_42 : p4 := by
              exact assump_30
            let assump_38 := assump_29 assump_42
            apply False.elim assump_38


theorem file91_21973 : ((((((False → False) → False) ∧ ((False → False) → (False → False))) → False) → False) → False) := by
  intro assump_1
  have assump_27 : ((((False → False) → False) ∧ ((False → False) → (False → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_28 : (False → False) := by
        intro assump_18
        apply False.elim assump_18
      let assump_17 := assump_6 assump_28
      apply False.elim assump_17
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p2 p0 p1 p5 : Prop)
theorem file91_22565 : ((((((False ∧ p5) ∨ (False → p5)) ∨ ((p0 ∧ p1) ∨ (p1 → False))) ∨ (((p2 ∧ False) ∧ (p2 → True)) → False)) → False) → False) := by
  intro assump_5
  have assump_15 : ((((False ∧ p5) ∨ (False → p5)) ∨ ((p0 ∧ p1) ∨ (p1 → False))) ∨ (((p2 ∧ False) ∧ (p2 → True)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p1 p3 p7 p0 p4 p5 : Prop)
theorem file91_23066 : (((((p1 → p1) ∨ (p5 ∧ p0)) → ((True ∧ p3) ∨ (p7 → False))) ∧ (((p4 ∨ p4) ∨ (p4 → p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((p4 ∨ p4) ∨ (p4 → p1)) := by
      apply Or.inr
      intro assump_9
      have assump_21 : ((p4 ∨ p4) ∨ (p4 → p1)) := by
        apply Or.inl
        apply Or.inl
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p4 p1 p6 p5 p0 p3 p2 : Prop)
theorem file91_23661 : (((((p1 → False) ∧ (False ∨ False)) ∧ ((p5 → False) ∨ (False ∨ p0))) → False) ∨ ((((p0 ∧ p2) ∨ (p3 → False)) ∨ ((p4 ∨ True) ∧ (p5 → p4))) ∧ (((True → p0) ∧ (p2 → p6)) → ((p5 → False) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        apply False.elim assump_9


variable (p6 p4 p2 p3 p5 p7 : Prop)
theorem file91_24210 : (((((p3 → False) → (False → False)) → False) → (((p6 ∧ p3) → (p4 → False)) → False)) ∨ ((((False → True) → (p2 ∨ p3)) ∨ ((False → p5) ∧ (p2 ∧ p7))) ∧ (((p3 ∧ p5) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_15 : ((p3 → False) → (False → False)) := by
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_15
  apply False.elim assump_7


variable (p3 p6 p5 p4 p7 : Prop)
theorem file91_24695 : (((((p3 → False) → (p4 ∧ False)) ∧ ((False ∧ p4) ∧ (p7 → True))) → (((p7 ∨ p4) → False) → ((p7 ∧ True) ∧ (p3 ∧ p5)))) ∨ ((((False → False) ∧ (p6 ∧ p5)) → False) → False)) := by
  apply Or.inl
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
        apply False.elim assump_11
  apply True.intro
  apply And.intro
  cases assump_1
  case intro assump_17 assump_18 =>
    cases assump_18
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        apply False.elim assump_23
  cases assump_1
  case intro assump_29 assump_30 =>
    cases assump_30
    case intro assump_33 assump_34 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        apply False.elim assump_35


variable (p2 p1 p7 p0 p6 p5 p4 : Prop)
theorem file91_25676 : (((((p1 ∨ p5) → False) ∧ ((False → False) → False)) → (((p6 → False) → (p6 ∧ p1)) → ((p1 ∨ p6) → (p6 → False)))) ∨ ((((p7 ∧ p1) → (p1 ∨ p0)) ∨ ((p4 ∨ p7) → False)) ∧ (((p1 → p2) ∨ (p7 → p1)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_1
    case intro assump_13 assump_14 =>
      have assump_43 : (False → False) := by
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_14 assump_43
      apply False.elim assump_19
  case inr assump_8 =>
    cases assump_1
    case intro assump_30 assump_31 =>
      have assump_44 : (False → False) := by
        intro assump_37
        apply False.elim assump_37
      let assump_36 := assump_31 assump_44
      apply False.elim assump_36


variable (p0 p6 p3 p7 : Prop)
theorem file91_26558 : (((((p7 ∨ p3) ∨ (p3 → p0)) ∨ ((p3 → p7) → (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p7 ∨ p3) ∨ (p3 → p0)) ∨ ((p3 → p7) → (p6 → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : (((p7 ∨ p3) ∨ (p3 → p0)) ∨ ((p3 → p7) → (p6 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p3 p6 p7 p0 p1 : Prop)
theorem file91_27143 : ((((((p7 → p1) ∨ (p0 → False)) → False) → (((p3 ∧ p2) → False) → ((p1 → False) ∧ (p6 → False)))) ∧ ((((p0 ∨ p1) → False) → ((False ∧ p6) → (p2 → p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p0 ∨ p1) → False) → ((False ∧ p6) → (p2 → p6))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p2 p6 p4 p5 p0 p3 : Prop)
theorem file91_27756 : (((((p4 ∨ p5) → (p5 ∧ p0)) ∧ ((p5 → True) → False)) → False) ∨ ((((p3 ∧ p3) ∨ (p4 → p6)) → ((False ∧ True) ∨ (p0 ∨ True))) ∨ (((False → False) ∧ (p4 → p5)) ∨ ((p6 ∧ p0) ∨ (p2 → p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (p5 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p7 p4 p5 p2 p0 p6 p3 p1 : Prop)
theorem file91_28248 : ((((((p5 ∨ p6) ∨ (p2 → p6)) ∨ ((p3 ∧ p5) ∧ (p6 ∨ p4))) → False) ∧ ((((p7 ∧ p4) → False) ∧ ((p4 ∨ p1) ∧ (False ∧ p6))) ∧ (((p1 ∧ p2) → (p1 ∨ p0)) → ((p7 → p0) → False)))) → False) := by
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
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
          case inr assump_15 =>
            cases assump_13
            case intro assump_24 assump_25 =>
              apply False.elim assump_24


variable (p4 p3 p1 p0 p6 : Prop)
theorem file91_29057 : (((((p1 ∨ p0) → False) → ((p3 ∨ p1) ∨ (p3 → p4))) → (((p1 → False) ∧ (True ∧ p4)) → ((p6 ∧ False) → (p0 → False)))) ∨ ((((p1 ∨ p1) → (p3 ∧ False)) → ((p1 ∧ p0) ∧ (False ∧ False))) ∧ (((p0 → False) → (p3 ∨ p1)) ∨ ((True → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    apply False.elim assump_8


variable (p3 p4 p0 p2 p5 p6 p7 : Prop)
theorem file91_29530 : (((((p4 ∧ p7) ∧ (p5 → p5)) → ((True → False) → (True → p3))) ∧ (((True ∧ p7) → (p0 ∨ p6)) ∧ ((True ∧ p2) ∧ (p2 → False)))) → ((((False → False) → (p3 ∧ p7)) ∧ ((False ∨ True) → (True ∨ False))) ∧ (((p5 ∨ p2) ∧ (p3 → False)) ∨ ((p4 ∧ True) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          have assump_102 : p2 := by
            exact assump_16
          let assump_23 := assump_14 assump_102
          apply False.elim assump_23
  cases assump_1
  case intro assump_29 assump_30 =>
    cases assump_30
    case intro assump_33 assump_34 =>
      cases assump_34
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          have assump_103 : p2 := by
            exact assump_40
          let assump_47 := assump_38 assump_103
          apply False.elim assump_47
  intro assump_51
  cases assump_51
  case inl assump_52 =>
    apply False.elim assump_52
  case inr assump_53 =>
    cases assump_1
    case intro assump_58 assump_59 =>
      cases assump_59
      case intro assump_62 assump_63 =>
        cases assump_63
        case intro assump_66 assump_67 =>
          cases assump_66
          case intro assump_68 assump_69 =>
            apply Or.inl
            apply True.intro
  cases assump_1
  case intro assump_76 assump_77 =>
    cases assump_77
    case intro assump_80 assump_81 =>
      cases assump_81
      case intro assump_84 assump_85 =>
        cases assump_84
        case intro assump_86 assump_87 =>
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_87
          intro assump_94
          have assump_104 : p2 := by
            exact assump_87
          let assump_98 := assump_85 assump_104
          apply False.elim assump_98


variable (p1 p6 p5 p0 p3 p4 p2 p7 : Prop)
theorem file91_31652 : ((((((p7 ∨ p3) ∨ (p0 → False)) → ((p2 ∧ p5) → False)) ∧ (((p6 ∨ True) ∨ (p5 ∧ p3)) → False)) ∨ ((((p0 → p0) → False) ∧ ((p0 ∧ p4) ∧ (p5 ∧ p5))) ∧ (((p0 ∨ False) → (p0 → False)) ∧ ((p7 → False) ∧ (p1 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_51 : ((p6 ∨ True) ∨ (p5 ∧ p3)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_10 := assump_5 assump_51
      apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            cases assump_21
            case intro assump_28 assump_29 =>
              cases assump_15
              case intro assump_34 assump_35 =>
                cases assump_35
                case intro assump_38 assump_39 =>
                  have assump_52 : (p0 ∨ False) := by
                    apply Or.inl
                    exact assump_22
                  let assump_46 := assump_34 assump_52
                  have assump_53 : p0 := by
                    exact assump_22
                  let assump_47 := assump_46 assump_53
                  apply False.elim assump_47


variable (p4 p7 p0 p6 p2 : Prop)
theorem file91_33112 : (((((False ∨ False) → (False ∨ p6)) → ((p0 → p0) ∨ (False → False))) → False) → ((((p7 ∨ p2) ∨ (p4 ∧ p4)) ∧ ((False → False) → False)) → (((p7 → False) → (True → True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        have assump_64 : (((False ∨ False) → (False ∨ p6)) → ((p0 → p0) ∨ (False → False))) := by
          intro assump_19
          apply Or.inl
          intro assump_22
          exact assump_22
        let assump_18 := assump_1 assump_64
        apply False.elim assump_18
      case inr assump_11 =>
        have assump_65 : (((False ∨ False) → (False ∨ p6)) → ((p0 → p0) ∨ (False → False))) := by
          intro assump_35
          apply Or.inl
          intro assump_38
          exact assump_38
        let assump_34 := assump_1 assump_65
        apply False.elim assump_34
    case inr assump_9 =>
      cases assump_9
      case intro assump_44 assump_45 =>
        have assump_66 : (((False ∨ False) → (False ∨ p6)) → ((p0 → p0) ∨ (False → False))) := by
          intro assump_55
          apply Or.inl
          intro assump_58
          exact assump_58
        let assump_54 := assump_1 assump_66
        apply False.elim assump_54


variable (p0 p2 p6 : Prop)
theorem file91_34492 : ((((((p6 ∨ p2) → (p0 → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p6 ∨ p2) → (p0 → True)) → False) → False) := by
    intro assump_5
    have assump_18 : ((p6 ∨ p2) → (p0 → True)) := by
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_5 assump_18
    apply False.elim assump_8
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p6 p4 : Prop)
theorem file91_34975 : ((((((False → False) ∨ (False → False)) ∧ ((p4 ∨ True) → (p1 → p6))) → (((True ∨ p6) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_38 : ((((False → False) ∨ (False → False)) ∧ ((p4 ∨ True) → (p1 → p6))) → (((True ∨ p6) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        have assump_39 : (True ∨ p6) := by
          apply Or.inl
          apply True.intro
        let assump_20 := assump_6 assump_39
        apply False.elim assump_20
      case inr assump_12 =>
        have assump_40 : (True ∨ p6) := by
          apply Or.inl
          apply True.intro
        let assump_31 := assump_6 assump_40
        apply False.elim assump_31
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p5 p6 p4 p1 p7 : Prop)
theorem file91_35884 : (((((p6 ∨ p4) ∧ (p1 ∨ p7)) ∨ ((p5 → False) → (False → False))) → False) → False) := by
  intro assump_23
  have assump_34 : (((p6 ∨ p4) ∧ (p1 ∨ p7)) ∨ ((p5 → False) → (False → False))) := by
    apply Or.inr
    intro assump_27
    intro assump_28
    apply False.elim assump_28
  let assump_26 := assump_23 assump_34
  apply False.elim assump_26


variable (p7 p6 p1 p0 p4 p5 : Prop)
theorem file91_36291 : ((((((p7 → p0) → (True ∧ p7)) → ((p0 → False) → (p6 → False))) ∧ (((p7 → False) ∨ (True → False)) ∨ ((False ∧ p5) → (p0 ∧ True)))) ∧ ((((p6 → False) → (p7 → p0)) ∧ ((False → False) → False)) ∧ (((p1 ∨ True) → False) ∨ ((False → True) ∧ (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case inl assump_22 =>
                have assump_111 : (p1 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_26 := assump_22 assump_111
                apply False.elim assump_26
              case inr assump_23 =>
                cases assump_23
                case intro assump_30 assump_31 =>
                  have assump_112 : (False → False) := by
                    intro assump_39
                    apply False.elim assump_39
                  let assump_38 := assump_17 assump_112
                  apply False.elim assump_38
        case inr assump_11 =>
          cases assump_3
          case intro assump_47 assump_48 =>
            cases assump_47
            case intro assump_49 assump_50 =>
              cases assump_48
              case inl assump_55 =>
                have assump_113 : (p1 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_59 := assump_55 assump_113
                apply False.elim assump_59
              case inr assump_56 =>
                cases assump_56
                case intro assump_63 assump_64 =>
                  have assump_114 : (False → False) := by
                    intro assump_72
                    apply False.elim assump_72
                  let assump_71 := assump_50 assump_114
                  apply False.elim assump_71
      case inr assump_9 =>
        cases assump_3
        case intro assump_80 assump_81 =>
          cases assump_80
          case intro assump_82 assump_83 =>
            cases assump_81
            case inl assump_88 =>
              have assump_115 : (p1 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_92 := assump_88 assump_115
              apply False.elim assump_92
            case inr assump_89 =>
              cases assump_89
              case intro assump_96 assump_97 =>
                have assump_116 : (False → False) := by
                  intro assump_105
                  apply False.elim assump_105
                let assump_104 := assump_83 assump_116
                apply False.elim assump_104


variable (p6 p0 p5 p4 : Prop)
theorem file91_39212 : ((((((p5 ∨ p6) ∧ (p0 → False)) ∧ ((p4 ∧ p5) ∧ (p5 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_51 : ((((p5 ∨ p6) ∧ (p0 → False)) ∧ ((p4 ∧ p5) ∧ (p5 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_52 : p5 := by
                exact assump_19
              let assump_26 := assump_17 assump_52
              apply False.elim assump_26
        case inr assump_11 =>
          cases assump_7
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              have assump_53 : p5 := by
                exact assump_37
              let assump_44 := assump_35 assump_53
              apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p1 p0 p4 p3 p6 p7 : Prop)
theorem file91_40371 : ((((((p6 ∧ False) ∧ (p6 → False)) → False) ∧ (((p3 → False) ∨ (p6 ∧ p1)) ∨ ((p3 ∧ False) → False))) ∧ ((((p1 → False) → (p3 ∨ p0)) → ((p7 → False) ∨ (False → True))) ∧ (((p4 → True) ∨ (p1 ∨ False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            have assump_55 : ((p4 → True) ∨ (p1 ∨ False)) := by
              apply Or.inl
              intro assump_21
              apply True.intro
            let assump_20 := assump_15 assump_55
            apply False.elim assump_20
        case inr assump_11 =>
          cases assump_11
          case intro assump_25 assump_26 =>
            cases assump_3
            case intro assump_31 assump_32 =>
              have assump_56 : ((p4 → True) ∨ (p1 ∨ False)) := by
                apply Or.inl
                intro assump_38
                apply True.intro
              let assump_37 := assump_32 assump_56
              apply False.elim assump_37
      case inr assump_9 =>
        cases assump_3
        case intro assump_44 assump_45 =>
          have assump_57 : ((p4 → True) ∨ (p1 ∨ False)) := by
            apply Or.inl
            intro assump_51
            apply True.intro
          let assump_50 := assump_45 assump_57
          apply False.elim assump_50


variable (p6 p2 p1 p7 : Prop)
theorem file91_41927 : (((((p2 → True) → (p7 → False)) → False) ∧ (((p7 ∨ p1) → False) ∧ ((False ∧ True) ∧ (p6 ∨ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p3 p5 p7 p1 p4 p2 p6 : Prop)
theorem file91_42392 : ((((((p5 ∨ p4) → False) ∨ ((p6 → p3) → (p7 ∧ False))) → False) ∧ ((((p3 ∨ p3) ∨ (p3 → False)) → ((True → False) ∧ (p3 ∧ p1))) ∨ (((p6 ∨ p5) → (p2 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_34 : ((p3 ∨ p3) ∨ (p3 → False)) := by
        apply Or.inr
        intro assump_11
        have assump_35 : ((p3 ∨ p3) ∨ (p3 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_15 := assump_6 assump_35
        let assump_16 := And.left assump_15
        have assump_36 : True := by
          apply True.intro
        let assump_17 := assump_16 assump_36
        apply False.elim assump_17
      let assump_10 := assump_6 assump_34
      let assump_21 := And.left assump_10
      have assump_37 : True := by
        apply True.intro
      let assump_22 := assump_21 assump_37
      apply False.elim assump_22
    case inr assump_7 =>
      have assump_38 : ((p6 ∨ p5) → (p2 → True)) := by
        intro assump_29
        intro assump_30
        apply True.intro
      let assump_28 := assump_7 assump_38
      apply False.elim assump_28


variable (p0 p6 p4 p3 p7 p1 p2 p5 : Prop)
theorem file91_43660 : ((((((p7 ∨ p7) ∧ (p3 ∧ p4)) ∧ ((p0 ∧ p6) ∧ (p5 → p6))) ∨ (((p0 ∨ p1) → (p1 ∨ False)) ∧ ((False → p2) → (p0 ∧ p0)))) ∧ ((((True ∧ False) ∧ (False → False)) ∧ ((p0 ∨ True) → False)) ∧ (((p2 ∨ p2) ∧ (p5 → False)) ∧ ((p0 → False) ∧ (p7 ∨ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
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
                  cases assump_3
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case intro assump_34 assump_35 =>
                        cases assump_34
                        case intro assump_36 assump_37 =>
                          apply False.elim assump_37
          case inr assump_11 =>
            cases assump_9
            case intro assump_44 assump_45 =>
              cases assump_7
              case intro assump_50 assump_51 =>
                cases assump_50
                case intro assump_52 assump_53 =>
                  cases assump_3
                  case intro assump_60 assump_61 =>
                    cases assump_60
                    case intro assump_62 assump_63 =>
                      cases assump_62
                      case intro assump_64 assump_65 =>
                        cases assump_64
                        case intro assump_66 assump_67 =>
                          apply False.elim assump_67
    case inr assump_5 =>
      cases assump_5
      case intro assump_72 assump_73 =>
        cases assump_3
        case intro assump_78 assump_79 =>
          cases assump_78
          case intro assump_80 assump_81 =>
            cases assump_80
            case intro assump_82 assump_83 =>
              cases assump_82
              case intro assump_84 assump_85 =>
                apply False.elim assump_85


variable (p1 p4 p6 : Prop)
theorem file91_46011 : (((((p1 → False) → (False → False)) → False) ∨ (((p4 ∧ p6) → (p4 ∧ p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_33 : ((p1 → False) → (False → False)) := by
      intro assump_7
      intro assump_8
      apply False.elim assump_8
    let assump_6 := assump_2 assump_33
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_34 : ((p4 ∧ p6) → (p4 ∧ p6)) := by
      intro assump_17
      apply And.intro
      cases assump_17
      case intro assump_18 assump_19 =>
        exact assump_18
      cases assump_17
      case intro assump_24 assump_25 =>
        exact assump_25
    let assump_16 := assump_3 assump_34
    apply False.elim assump_16


variable (p4 p6 p7 p0 p2 p5 p3 p1 : Prop)
theorem file91_46795 : ((((((p1 ∧ p6) ∧ (False → p0)) → ((True → p2) → (p0 ∨ False))) ∨ (((p5 ∧ p3) ∧ (False ∨ False)) ∧ ((p0 → p2) → False))) ∧ ((((p4 ∧ p7) → False) ∧ ((p1 ∧ p6) ∧ (True → False))) ∧ (((p6 → False) → False) → ((p7 ∨ p1) → False)))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              have assump_54 : ((p6 → False) → False) := by
                intro assump_27
                have assump_55 : p6 := by
                  exact assump_17
                let assump_30 := assump_27 assump_55
                apply False.elim assump_30
              let assump_26 := assump_9 assump_54
              have assump_56 : (p7 ∨ p1) := by
                apply Or.inr
                exact assump_16
              let assump_34 := assump_26 assump_56
              apply False.elim assump_34
    case inr assump_5 =>
      cases assump_5
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            cases assump_41
            case inl assump_48 =>
              apply False.elim assump_48
            case inr assump_49 =>
              apply False.elim assump_49


variable (p5 p2 p3 p7 p0 p1 p4 p6 : Prop)
theorem file91_48397 : (((((p5 → False) → (p0 ∧ p1)) → ((False → p5) ∧ (False → False))) ∨ (((p7 ∨ p2) → False) ∧ ((p1 → False) ∨ (p6 ∧ p3)))) ∧ ((((p1 → True) ∧ (p2 → p0)) ∧ ((True ∧ False) ∧ (p4 → False))) → (((True → False) ∨ (p2 ∧ p7)) ∨ ((p0 ∧ p4) → (p6 → p2))))) := by
  apply And.intro
  apply Or.inl
  intro assump_5
  apply And.intro
  intro assump_6
  apply False.elim assump_6
  intro assump_9
  apply False.elim assump_9
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_14
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply False.elim assump_24


variable (p0 p3 p5 p2 p1 p4 : Prop)
theorem file91_49162 : ((((((p1 → False) ∧ (p0 ∧ p5)) → ((p5 ∧ p1) → False)) ∨ (((p2 → p3) → (p1 → p5)) → ((p4 ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p1 → False) ∧ (p0 ∧ p5)) → ((p5 ∧ p1) → False)) ∨ (((p2 → p3) → (p1 → p5)) → ((p4 ∧ p0) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          have assump_33 : p1 := by
            exact assump_8
          let assump_25 := assump_13 assump_33
          apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p3 p1 p7 p4 p2 p5 p0 : Prop)
theorem file91_49948 : ((((((True → False) → (p4 ∨ True)) ∧ ((p7 ∧ False) → (p1 ∧ p1))) → (((p7 ∨ p2) ∨ (p2 → p3)) ∨ ((p7 → p2) → False))) ∧ ((((p7 → False) ∧ (p0 → True)) → ((True → False) ∧ (p5 ∨ p7))) ∧ (((False ∧ p0) → (p7 → p5)) → False))) → False) := by
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      have assump_45 : ((False ∧ p0) → (p7 → p5)) := by
        intro assump_34
        intro assump_35
        cases assump_34
        case intro assump_38 assump_39 =>
          apply False.elim assump_38
      let assump_33 := assump_28 assump_45
      apply False.elim assump_33


variable (p2 p1 p7 p3 p6 p5 : Prop)
theorem file91_50658 : (((((p7 ∨ p1) → False) → False) → False) → ((((p6 → False) ∧ (False ∧ False)) → False) ∨ (((p5 → p2) → False) ∧ ((p6 ∨ p6) ∧ (p1 → p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p6 p5 p0 p1 p4 p3 p2 p7 : Prop)
theorem file91_51057 : (((((p6 → False) → (True → p2)) → ((p3 → False) ∨ (p5 → True))) ∧ (((True ∧ False) ∧ (True → p0)) ∨ ((True ∨ p7) → False))) → ((((p7 ∧ False) → False) ∧ ((p1 ∨ p2) ∨ (p4 ∧ p4))) ∧ (((p1 ∧ True) ∨ (p0 ∧ p4)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4
  cases assump_1
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
    case inr assump_14 =>
      have assump_84 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_25 := assump_14 assump_84
      apply False.elim assump_25
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_1
      case intro assump_38 assump_39 =>
        cases assump_39
        case inl assump_42 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              apply False.elim assump_47
        case inr assump_43 =>
          have assump_85 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_54 := assump_43 assump_85
          apply False.elim assump_54
  case inr assump_31 =>
    cases assump_31
    case intro assump_58 assump_59 =>
      cases assump_1
      case intro assump_64 assump_65 =>
        cases assump_65
        case inl assump_68 =>
          cases assump_68
          case intro assump_70 assump_71 =>
            cases assump_70
            case intro assump_72 assump_73 =>
              apply False.elim assump_73
        case inr assump_69 =>
          have assump_86 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_80 := assump_69 assump_86
          apply False.elim assump_80


variable (p7 p3 : Prop)
theorem file91_53158 : ((((((p7 → p7) ∨ (p3 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 → p7) ∨ (p3 → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p7 → p7) ∨ (p3 → False)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p2 p6 p7 p5 p3 p4 : Prop)
theorem file91_53651 : (((((False ∧ p3) → False) → False) → (((p4 → p1) → (p6 ∨ p4)) ∧ ((p3 ∧ True) ∧ (p3 ∧ p4)))) ∨ ((((p7 ∨ p3) → False) → ((p2 → p2) ∨ (p3 → False))) ∧ (((p4 ∧ p5) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_49 : ((False ∧ p3) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_7 := assump_1 assump_49
  apply False.elim assump_7
  apply And.intro
  apply And.intro
  have assump_50 : ((False ∧ p3) → False) := by
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      apply False.elim assump_20
  let assump_18 := assump_1 assump_50
  apply False.elim assump_18
  apply True.intro
  apply And.intro
  have assump_51 : ((False ∧ p3) → False) := by
    intro assump_30
    cases assump_30
    case intro assump_31 assump_32 =>
      apply False.elim assump_31
  let assump_29 := assump_1 assump_51
  apply False.elim assump_29
  have assump_52 : ((False ∧ p3) → False) := by
    intro assump_41
    cases assump_41
    case intro assump_42 assump_43 =>
      apply False.elim assump_42
  let assump_40 := assump_1 assump_52
  apply False.elim assump_40


variable (p4 p1 p0 p7 : Prop)
theorem file91_54929 : (((((p1 ∨ False) ∨ (p0 ∨ True)) → ((False → False) ∨ (p4 → p7))) → False) → False) := by
  intro assump_5
  have assump_36 : (((p1 ∨ False) ∨ (p0 ∨ True)) → ((False → False) ∨ (p4 → p7))) := by
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        apply Or.inl
        intro assump_16
        apply False.elim assump_16
      case inr assump_13 =>
        apply False.elim assump_13
    case inr assump_11 =>
      cases assump_11
      case inl assump_21 =>
        apply Or.inl
        intro assump_25
        apply False.elim assump_25
      case inr assump_22 =>
        apply Or.inl
        intro assump_30
        apply False.elim assump_30
  let assump_8 := assump_5 assump_36
  apply False.elim assump_8


variable (p0 p3 p7 p4 p5 p1 p2 : Prop)
theorem file91_55772 : (((((False → False) → False) → ((True ∨ p7) → False)) → False) → ((((True ∨ p2) ∨ (p2 → p2)) → False) → (((p0 → False) → (p5 → False)) ∨ ((True → p1) → (p4 ∧ p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  have assump_45 : (((False → False) → False) → ((True ∨ p7) → False)) := by
    intro assump_16
    intro assump_17
    cases assump_17
    case inl assump_18 =>
      have assump_46 : (False → False) := by
        intro assump_25
        apply False.elim assump_25
      let assump_24 := assump_16 assump_46
      apply False.elim assump_24
    case inr assump_19 =>
      have assump_47 : (False → False) := by
        intro assump_36
        apply False.elim assump_36
      let assump_35 := assump_16 assump_47
      apply False.elim assump_35
  let assump_15 := assump_1 assump_45
  apply False.elim assump_15


variable (p2 p6 p0 p7 p1 p5 p4 : Prop)
theorem file91_56706 : ((((((p7 ∨ p0) ∨ (p6 ∨ p2)) → False) → (((p0 ∧ p2) ∨ (p2 ∨ True)) ∨ ((p4 ∨ p4) ∧ (p1 ∨ p1)))) ∧ ((((p6 → False) ∧ (p5 → False)) → ((p2 → False) ∧ (p2 ∧ False))) ∧ (((p7 ∧ p7) ∨ (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((p7 ∧ p7) ∨ (False → False)) := by
        apply Or.inr
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p1 p4 p7 p2 : Prop)
theorem file91_57317 : (((((True → p2) ∨ (False ∨ p1)) → ((False ∧ False) ∧ (p4 → False))) ∧ (((p1 → False) → False) ∧ ((p1 → False) ∧ (p7 → False)))) → False) := by
  intro assump_41
  cases assump_41
  case intro assump_42 assump_43 =>
    cases assump_43
    case intro assump_46 assump_47 =>
      cases assump_47
      case intro assump_50 assump_51 =>
        have assump_71 : (p1 → False) := by
          intro assump_59
          have assump_72 : p1 := by
            exact assump_59
          let assump_64 := assump_50 assump_72
          apply False.elim assump_64
        let assump_58 := assump_46 assump_71
        apply False.elim assump_58


variable (p0 p2 p5 p6 p7 p4 p1 p3 : Prop)
theorem file91_58016 : (((((False ∧ p1) ∧ (p4 ∧ p1)) ∧ ((p6 ∨ p4) → False)) ∧ (((p0 → False) ∧ (p1 → False)) ∨ ((True → p6) ∨ (True → False)))) → ((((p2 → p3) → (True → p5)) → ((p5 → p3) ∧ (False ∧ p2))) ∧ (((True → False) → (p4 → p7)) → False))) := by
  intro assump_7
  apply And.intro
  intro assump_8
  apply And.intro
  intro assump_9
  cases assump_7
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
  apply And.intro
  cases assump_7
  case intro assump_26 assump_27 =>
    cases assump_26
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          apply False.elim assump_32
  cases assump_7
  case intro assump_38 assump_39 =>
    cases assump_38
    case intro assump_40 assump_41 =>
      cases assump_40
      case intro assump_42 assump_43 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          apply False.elim assump_44
  intro assump_48
  cases assump_7
  case intro assump_51 assump_52 =>
    cases assump_51
    case intro assump_53 assump_54 =>
      cases assump_53
      case intro assump_55 assump_56 =>
        cases assump_55
        case intro assump_57 assump_58 =>
          apply False.elim assump_57


variable (p0 p1 p2 p3 p4 : Prop)
theorem file91_59530 : ((((((True → False) ∨ (p2 → False)) ∧ ((p1 → p2) ∧ (p0 → False))) → (((p4 ∨ p3) ∧ (p2 ∧ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_94 : ((((True → False) ∨ (p2 → False)) ∧ ((p1 → p2) ∧ (p0 → False))) → (((p4 ∨ p3) ∧ (p2 ∧ p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_5
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_20
              case intro assump_25 assump_26 =>
                have assump_95 : True := by
                  apply True.intro
                let assump_33 := assump_21 assump_95
                apply False.elim assump_33
            case inr assump_22 =>
              cases assump_20
              case intro assump_39 assump_40 =>
                have assump_96 : p2 := by
                  exact assump_13
                let assump_47 := assump_22 assump_96
                apply False.elim assump_47
      case inr assump_10 =>
        cases assump_8
        case intro assump_53 assump_54 =>
          cases assump_5
          case intro assump_59 assump_60 =>
            cases assump_59
            case inl assump_61 =>
              cases assump_60
              case intro assump_65 assump_66 =>
                have assump_97 : True := by
                  apply True.intro
                let assump_73 := assump_61 assump_97
                apply False.elim assump_73
            case inr assump_62 =>
              cases assump_60
              case intro assump_79 assump_80 =>
                have assump_98 : p2 := by
                  exact assump_53
                let assump_87 := assump_62 assump_98
                apply False.elim assump_87
  let assump_4 := assump_1 assump_94
  apply False.elim assump_4


variable (p6 p0 p5 p4 p2 p3 p1 : Prop)
theorem file91_61563 : (((((p5 → False) → (p2 ∧ p4)) ∨ ((True ∧ p3) → (p0 → False))) → (((p0 ∨ p3) ∨ (True ∨ p4)) ∨ ((p1 ∧ False) ∨ (p1 → p1)))) ∧ ((((True ∨ p5) → False) ∧ ((p6 ∨ p5) ∨ (p2 ∨ p0))) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        have assump_47 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_20 := assump_9 assump_47
        apply False.elim assump_20
      case inr assump_16 =>
        have assump_48 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_27 := assump_9 assump_48
        apply False.elim assump_27
    case inr assump_14 =>
      cases assump_14
      case inl assump_31 =>
        have assump_49 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_36 := assump_9 assump_49
        apply False.elim assump_36
      case inr assump_32 =>
        have assump_50 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_43 := assump_9 assump_50
        apply False.elim assump_43


variable (p7 p3 p4 p2 p6 p0 p1 : Prop)
theorem file91_63044 : (((((False ∧ p1) → (p2 ∧ p2)) ∨ ((p7 → False) ∨ (p4 → p6))) ∨ (((False → False) ∧ (p4 ∧ p3)) ∧ ((p3 → False) → (False ∧ p2)))) ∨ ((((True → False) → (p0 ∨ p0)) ∧ ((p0 ∨ p1) ∨ (p6 → p6))) → (((p1 ∨ p1) → (p1 ∧ p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  cases assump_1
  case intro assump_6 assump_7 =>
    apply False.elim assump_6


variable (p5 p1 p7 : Prop)
theorem file91_63568 : (((((p5 → False) ∨ (p1 → p5)) → False) ∧ (((p5 ∧ False) ∨ (True → False)) ∧ ((p7 → p7) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_9 =>
        have assump_27 : (p7 → p7) := by
          intro assump_21
          exact assump_21
        let assump_20 := assump_7 assump_27
        apply False.elim assump_20


variable (p1 p7 p3 p4 : Prop)
theorem file91_64207 : (((((False → False) → False) ∧ ((p7 ∧ p4) ∧ (p3 → False))) ∧ (((True → True) → False) ∨ ((p4 ∨ p1) ∨ (p7 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_3
          case inl assump_18 =>
            have assump_63 : (True → True) := by
              intro assump_23
              apply True.intro
            let assump_22 := assump_18 assump_63
            apply False.elim assump_22
          case inr assump_19 =>
            cases assump_19
            case inl assump_27 =>
              cases assump_27
              case inl assump_29 =>
                have assump_64 : (False → False) := by
                  intro assump_38
                  apply False.elim assump_38
                let assump_37 := assump_4 assump_64
                apply False.elim assump_37
              case inr assump_30 =>
                have assump_65 : (False → False) := by
                  intro assump_51
                  apply False.elim assump_51
                let assump_50 := assump_4 assump_65
                apply False.elim assump_50
            case inr assump_28 =>
              have assump_66 : p7 := by
                exact assump_10
              let assump_59 := assump_28 assump_66
              apply False.elim assump_59


variable (p2 p7 p6 p0 p5 p3 p1 p4 : Prop)
theorem file91_65759 : (((((p4 ∨ p0) → (p0 ∧ True)) → ((p4 ∧ p0) → (False ∧ p4))) ∨ (((p3 ∧ p1) → (p0 → p2)) ∨ ((p3 ∧ p0) → False))) → ((((True → False) ∧ (p3 ∧ p3)) → ((p7 → True) ∧ (False ∨ True))) ∧ (((p6 ∧ False) → False) ∨ ((p5 ∨ p7) ∨ (p6 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  apply True.intro
  cases assump_2
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      cases assump_1
      case inl assump_14 =>
        apply Or.inr
        apply True.intro
      case inr assump_15 =>
        cases assump_15
        case inl assump_18 =>
          apply Or.inr
          apply True.intro
        case inr assump_19 =>
          apply Or.inr
          apply True.intro
  cases assump_1
  case inl assump_24 =>
    apply Or.inl
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      apply False.elim assump_30
  case inr assump_25 =>
    cases assump_25
    case inl assump_35 =>
      apply Or.inl
      intro assump_39
      cases assump_39
      case intro assump_40 assump_41 =>
        apply False.elim assump_41
    case inr assump_36 =>
      apply Or.inl
      intro assump_48
      cases assump_48
      case intro assump_49 assump_50 =>
        apply False.elim assump_50


variable (p0 p1 p4 p7 p2 : Prop)
theorem file91_67117 : (((((p4 ∧ p1) ∨ (p7 ∨ p2)) ∨ ((p0 ∨ False) → (True → True))) → False) → ((((p0 ∨ p1) → (p2 → False)) → False) ∨ (((p4 ∨ p2) ∧ (p7 → False)) ∧ ((p1 ∧ p4) ∧ (p0 ∨ p0))))) := by
  intro assump_19
  apply Or.inl
  intro assump_22
  have assump_32 : (((p4 ∧ p1) ∨ (p7 ∨ p2)) ∨ ((p0 ∨ False) → (True → True))) := by
    apply Or.inr
    intro assump_27
    intro assump_28
    apply True.intro
  let assump_26 := assump_19 assump_32
  apply False.elim assump_26


variable (p3 p6 p7 p5 p1 p0 p2 : Prop)
theorem file91_67636 : (((((p7 ∧ False) → (p3 ∧ p7)) → False) ∧ (((p7 ∨ p1) → (p6 → False)) ∧ ((p2 ∧ True) → (p0 → False)))) → ((((p0 ∧ p5) → (p1 → False)) → False) ∧ (((False → p7) → (p3 → False)) ∧ ((True → p0) → (p0 ∧ p0))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_132 : ((p7 ∧ False) → (p3 ∧ p7)) := by
        intro assump_18
        apply And.intro
        cases assump_18
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
        cases assump_18
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
      let assump_17 := assump_5 assump_132
      apply False.elim assump_17
  apply And.intro
  intro assump_34
  intro assump_35
  cases assump_1
  case intro assump_40 assump_41 =>
    cases assump_41
    case intro assump_44 assump_45 =>
      have assump_133 : ((p7 ∧ False) → (p3 ∧ p7)) := by
        intro assump_53
        apply And.intro
        cases assump_53
        case intro assump_54 assump_55 =>
          apply False.elim assump_55
        cases assump_53
        case intro assump_60 assump_61 =>
          apply False.elim assump_61
      let assump_52 := assump_40 assump_133
      apply False.elim assump_52
  intro assump_69
  apply And.intro
  cases assump_1
  case intro assump_72 assump_73 =>
    cases assump_73
    case intro assump_76 assump_77 =>
      have assump_134 : ((p7 ∧ False) → (p3 ∧ p7)) := by
        intro assump_85
        apply And.intro
        cases assump_85
        case intro assump_86 assump_87 =>
          apply False.elim assump_87
        cases assump_85
        case intro assump_92 assump_93 =>
          apply False.elim assump_93
      let assump_84 := assump_72 assump_134
      apply False.elim assump_84
  cases assump_1
  case intro assump_103 assump_104 =>
    cases assump_104
    case intro assump_107 assump_108 =>
      have assump_135 : ((p7 ∧ False) → (p3 ∧ p7)) := by
        intro assump_116
        apply And.intro
        cases assump_116
        case intro assump_117 assump_118 =>
          apply False.elim assump_118
        cases assump_116
        case intro assump_123 assump_124 =>
          apply False.elim assump_124
      let assump_115 := assump_103 assump_135
      apply False.elim assump_115


variable (p6 p4 p5 p0 p7 p1 : Prop)
theorem file91_70058 : (((((False → False) ∨ (p1 → p4)) → False) → (((p7 → True) → False) ∨ ((p0 ∧ p6) → (p1 ∨ p7)))) ∨ ((((p6 → p5) → False) ∨ ((p6 ∨ p1) → (p5 → False))) ∨ (((p1 → False) ∨ (p1 ∧ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_15 : ((False → False) ∨ (p1 → p4)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p7 p2 p0 p3 p4 p1 : Prop)
theorem file91_70564 : (((((p0 ∨ True) → False) → ((p0 ∧ p1) ∧ (p0 ∨ p4))) ∧ (((p1 → False) → (True ∨ p0)) ∨ ((p4 ∨ True) ∧ (False → False)))) ∨ ((((p4 ∧ p2) ∨ (p3 → False)) → False) ∧ (((True → False) → (p4 → False)) ∨ ((p7 → p1) → (p1 → False))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_23 : (p0 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4
  have assump_24 : (p0 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_10 := assump_1 assump_24
  apply False.elim assump_10
  have assump_25 : (p0 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_16 := assump_1 assump_25
  apply False.elim assump_16
  apply Or.inl
  intro assump_20
  apply Or.inl
  apply True.intro


variable (p7 : Prop)
theorem file91_71419 : (((((False → p7) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p7) → False) → False) := by
    intro assump_5
    have assump_19 : (False → p7) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p0 p2 p6 p5 p7 p1 : Prop)
theorem file91_71862 : ((((((p4 ∧ p7) → (p6 → False)) → False) ∨ (((False ∧ p7) ∧ (p1 → False)) → False)) ∧ ((((False → p5) ∨ (True → p5)) ∨ ((p0 → p4) ∨ (p2 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_28 : (((False → p5) ∨ (True → p5)) ∨ ((p0 → p4) ∨ (p2 ∨ p6))) := by
        apply Or.inl
        apply Or.inl
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_28
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_29 : (((False → p5) ∨ (True → p5)) ∨ ((p0 → p4) ∨ (p2 ∨ p6))) := by
        apply Or.inl
        apply Or.inl
        intro assump_22
        apply False.elim assump_22
      let assump_21 := assump_3 assump_29
      apply False.elim assump_21


variable (p4 p5 p3 p0 p7 p2 : Prop)
theorem file91_72751 : (((((p2 ∨ p7) ∧ (False → False)) → False) → (((p0 → False) → (p2 → False)) → ((False ∨ True) ∨ (p4 ∨ p5)))) ∨ ((((p3 ∧ p7) ∧ (True → True)) ∨ ((p5 ∧ p5) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p6 p2 p1 p3 p4 p7 : Prop)
theorem file91_73088 : ((((((p3 → p7) → (False → False)) → ((False → p6) ∨ (p4 ∧ False))) ∨ (((True → False) ∨ (p2 ∨ p4)) ∨ ((p3 ∨ p1) ∧ (p6 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p3 → p7) → (False → False)) → ((False → p6) ∨ (p4 ∧ False))) ∨ (((True → False) ∨ (p2 ∨ p4)) ∨ ((p3 ∨ p1) ∧ (p6 ∧ p7)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p5 p2 p1 p3 p0 p4 : Prop)
theorem file91_73636 : (((((p4 ∧ True) ∧ (p1 ∧ p3)) → ((p0 ∧ p7) → False)) → (((p3 → False) → False) → ((p2 ∧ False) → False))) ∨ ((((True ∨ p5) → (p2 ∧ p3)) → False) ∧ (((p2 ∧ p1) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5


variable (p0 p3 p5 p6 p2 p1 : Prop)
theorem file91_74027 : (((((p6 ∨ False) ∨ (False ∨ p6)) → ((p0 → False) ∨ (p0 → True))) ∨ (((p5 → False) ∨ (p2 → False)) ∧ ((p5 → False) ∨ (p1 → p5)))) → ((((p0 ∨ False) ∨ (True ∧ p3)) ∧ ((p3 → True) ∧ (False ∧ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_4
        case intro assump_11 assump_12 =>
          cases assump_12
          case intro assump_15 assump_16 =>
            apply False.elim assump_15
      case inr assump_8 =>
        apply False.elim assump_8
    case inr assump_6 =>
      cases assump_6
      case intro assump_21 assump_22 =>
        cases assump_4
        case intro assump_27 assump_28 =>
          cases assump_28
          case intro assump_31 assump_32 =>
            apply False.elim assump_31


variable (p0 p4 p3 p6 p2 p1 p5 : Prop)
theorem file91_74974 : (((((p5 → False) ∧ (p4 ∧ p0)) → ((True ∧ p2) → (False → False))) ∨ (((p6 → False) ∨ (p2 ∨ p3)) → False)) ∨ ((((p1 → False) ∨ (p5 ∨ p6)) ∨ ((p5 → p6) ∧ (True ∧ p5))) ∨ (((p5 ∨ False) ∨ (False ∧ p1)) → ((True ∨ True) ∧ (False ∧ False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p6 p2 : Prop)
theorem file91_75374 : (((((p6 ∨ p2) → False) → ((p6 → False) ∨ (p2 → False))) ∧ (((False → False) ∨ (p6 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (p6 → False)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p4 p6 p7 : Prop)
theorem file91_75814 : (((((p4 ∧ p3) ∧ (p6 ∨ True)) ∨ ((p7 → p7) ∨ (False → False))) → False) → False) := by
  intro assump_24
  have assump_34 : (((p4 ∧ p3) ∧ (p6 ∨ True)) ∨ ((p7 → p7) ∨ (False → False))) := by
    apply Or.inr
    apply Or.inl
    intro assump_28
    exact assump_28
  let assump_27 := assump_24 assump_34
  apply False.elim assump_27


variable (p3 p4 p0 p7 p2 p1 p5 p6 : Prop)
theorem file91_76211 : (((((p5 ∨ p6) ∧ (p4 ∨ p6)) ∧ ((True → p4) ∧ (False → p1))) → (((True → False) → (p3 → False)) ∧ ((False ∨ p3) → (p6 ∨ p4)))) ∨ ((((p0 ∧ False) → (p0 → False)) ∨ ((False → False) → False)) ∧ (((p3 ∨ p2) ∧ (False → p2)) ∨ ((p1 ∨ p3) → (p2 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case inl assump_16 =>
          cases assump_9
          case intro assump_20 assump_21 =>
            have assump_143 : True := by
              apply True.intro
            let assump_31 := assump_2 assump_143
            apply False.elim assump_31
        case inr assump_17 =>
          cases assump_9
          case intro assump_37 assump_38 =>
            have assump_144 : True := by
              apply True.intro
            let assump_48 := assump_2 assump_144
            apply False.elim assump_48
      case inr assump_13 =>
        cases assump_11
        case inl assump_54 =>
          cases assump_9
          case intro assump_58 assump_59 =>
            have assump_145 : True := by
              apply True.intro
            let assump_69 := assump_2 assump_145
            apply False.elim assump_69
        case inr assump_55 =>
          cases assump_9
          case intro assump_75 assump_76 =>
            have assump_146 : True := by
              apply True.intro
            let assump_86 := assump_2 assump_146
            apply False.elim assump_86
  intro assump_90
  cases assump_90
  case inl assump_91 =>
    apply False.elim assump_91
  case inr assump_92 =>
    cases assump_1
    case intro assump_97 assump_98 =>
      cases assump_97
      case intro assump_99 assump_100 =>
        cases assump_99
        case inl assump_101 =>
          cases assump_100
          case inl assump_105 =>
            cases assump_98
            case intro assump_109 assump_110 =>
              apply Or.inr
              exact assump_105
          case inr assump_106 =>
            cases assump_98
            case intro assump_117 assump_118 =>
              apply Or.inl
              exact assump_106
        case inr assump_102 =>
          cases assump_100
          case inl assump_125 =>
            cases assump_98
            case intro assump_129 assump_130 =>
              apply Or.inl
              exact assump_102
          case inr assump_126 =>
            cases assump_98
            case intro assump_137 assump_138 =>
              apply Or.inl
              exact assump_126


variable (p0 p2 p4 p5 p6 p3 p7 : Prop)
theorem file91_78924 : (((((p6 ∧ p7) → (p3 → False)) → ((p7 → False) → False)) → (((p5 → p2) ∧ (p5 ∧ False)) → ((p3 → p0) → False))) ∧ ((((p6 → False) ∧ (p6 ∧ p4)) → ((p6 → False) ∨ (True → False))) ∨ (((p6 → p0) → False) → False))) := by
  apply And.intro
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    cases assump_15
    case intro assump_18 assump_19 =>
      apply False.elim assump_19
  apply Or.inl
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      apply Or.inl
      intro assump_35
      have assump_45 : p6 := by
        exact assump_35
      let assump_41 := assump_25 assump_45
      apply False.elim assump_41


variable (p1 p6 p2 p3 p4 p5 p0 : Prop)
theorem file91_79737 : (((((p6 ∧ False) → False) ∨ ((p0 → False) → (p5 ∧ p0))) → (((p3 ∧ p5) → False) ∧ ((False ∧ p4) ∧ (p2 ∨ False)))) → ((((p6 ∨ p4) ∨ (p1 ∧ p6)) ∨ ((p3 ∧ p5) → (p3 ∨ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        have assump_89 : (((p6 ∧ False) → False) ∨ ((p0 → False) → (p5 ∧ p0))) := by
          apply Or.inl
          intro assump_14
          cases assump_14
          case intro assump_15 assump_16 =>
            apply False.elim assump_16
        let assump_13 := assump_1 assump_89
        let assump_21 := And.right assump_13
        let assump_23 := And.left assump_21
        let assump_24 := And.left assump_23
        apply False.elim assump_24
      case inr assump_8 =>
        have assump_90 : (((p6 ∧ False) → False) ∨ ((p0 → False) → (p5 ∧ p0))) := by
          apply Or.inl
          intro assump_33
          cases assump_33
          case intro assump_34 assump_35 =>
            apply False.elim assump_35
        let assump_32 := assump_1 assump_90
        let assump_40 := And.right assump_32
        let assump_42 := And.left assump_40
        let assump_43 := And.left assump_42
        apply False.elim assump_43
    case inr assump_6 =>
      cases assump_6
      case intro assump_47 assump_48 =>
        have assump_91 : (((p6 ∧ False) → False) ∨ ((p0 → False) → (p5 ∧ p0))) := by
          apply Or.inl
          intro assump_56
          cases assump_56
          case intro assump_57 assump_58 =>
            apply False.elim assump_58
        let assump_55 := assump_1 assump_91
        let assump_63 := And.right assump_55
        let assump_65 := And.left assump_63
        let assump_66 := And.left assump_65
        apply False.elim assump_66
  case inr assump_4 =>
    have assump_92 : (((p6 ∧ False) → False) ∨ ((p0 → False) → (p5 ∧ p0))) := by
      apply Or.inl
      intro assump_75
      cases assump_75
      case intro assump_76 assump_77 =>
        apply False.elim assump_77
    let assump_74 := assump_1 assump_92
    let assump_82 := And.right assump_74
    let assump_84 := And.left assump_82
    let assump_85 := And.left assump_84
    apply False.elim assump_85


variable (p1 p2 p3 p6 p4 : Prop)
theorem file91_82056 : ((((((p6 ∨ True) ∧ (p1 ∨ p2)) → False) → (((p4 → False) → (p1 → False)) ∨ ((False → False) ∨ (p1 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p6 ∨ True) ∧ (p1 ∨ p2)) → False) → (((p4 → False) → (p1 → False)) ∨ ((False → False) ∨ (p1 ∧ p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_24 : ((p6 ∨ True) ∧ (p1 ∨ p2)) := by
      apply And.intro
      apply Or.inr
      apply True.intro
      apply Or.inl
      exact assump_9
    let assump_16 := assump_5 assump_24
    apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p0 p1 p2 p5 p7 : Prop)
theorem file91_82759 : ((((((True → False) ∧ (False ∨ p7)) ∧ ((p5 → False) → False)) → (((False ∧ p2) → False) ∨ ((False ∨ p0) → (p1 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True → False) ∧ (False ∨ p7)) ∧ ((p5 → False) → False)) → (((False ∧ p2) → False) ∨ ((False ∨ p0) → (p1 ∧ p3)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          apply Or.inl
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p1 p6 p7 p5 p0 p2 p4 : Prop)
theorem file91_83600 : (((((p0 ∧ p0) ∧ (p1 ∧ False)) → False) → (((False → p7) → False) ∧ ((p1 → False) → (False → False)))) → ((((p5 ∧ p6) → False) ∧ ((False ∧ p6) → (p1 → False))) → (((p2 ∧ True) ∨ (p2 ∨ False)) → ((p4 → False) ∧ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_2
      case intro assump_15 assump_16 =>
        have assump_166 : (((p0 ∧ p0) ∧ (p1 ∧ False)) → False) := by
          intro assump_24
          cases assump_24
          case intro assump_25 assump_26 =>
            cases assump_25
            case intro assump_27 assump_28 =>
              cases assump_26
              case intro assump_33 assump_34 =>
                apply False.elim assump_34
        let assump_23 := assump_1 assump_166
        let assump_39 := And.left assump_23
        have assump_167 : (False → p7) := by
          intro assump_41
          apply False.elim assump_41
        let assump_40 := assump_39 assump_167
        apply False.elim assump_40
  case inr assump_8 =>
    cases assump_8
    case inl assump_47 =>
      cases assump_2
      case intro assump_51 assump_52 =>
        have assump_168 : (((p0 ∧ p0) ∧ (p1 ∧ False)) → False) := by
          intro assump_60
          cases assump_60
          case intro assump_61 assump_62 =>
            cases assump_61
            case intro assump_63 assump_64 =>
              cases assump_62
              case intro assump_69 assump_70 =>
                apply False.elim assump_70
        let assump_59 := assump_1 assump_168
        let assump_75 := And.left assump_59
        have assump_169 : (False → p7) := by
          intro assump_77
          apply False.elim assump_77
        let assump_76 := assump_75 assump_169
        apply False.elim assump_76
    case inr assump_48 =>
      apply False.elim assump_48
  intro assump_85
  cases assump_3
  case inl assump_88 =>
    cases assump_88
    case intro assump_90 assump_91 =>
      cases assump_2
      case intro assump_96 assump_97 =>
        have assump_170 : (((p0 ∧ p0) ∧ (p1 ∧ False)) → False) := by
          intro assump_105
          cases assump_105
          case intro assump_106 assump_107 =>
            cases assump_106
            case intro assump_108 assump_109 =>
              cases assump_107
              case intro assump_114 assump_115 =>
                apply False.elim assump_115
        let assump_104 := assump_1 assump_170
        let assump_120 := And.left assump_104
        have assump_171 : (False → p7) := by
          intro assump_122
          apply False.elim assump_122
        let assump_121 := assump_120 assump_171
        apply False.elim assump_121
  case inr assump_89 =>
    cases assump_89
    case inl assump_128 =>
      cases assump_2
      case intro assump_132 assump_133 =>
        have assump_172 : (((p0 ∧ p0) ∧ (p1 ∧ False)) → False) := by
          intro assump_141
          cases assump_141
          case intro assump_142 assump_143 =>
            cases assump_142
            case intro assump_144 assump_145 =>
              cases assump_143
              case intro assump_150 assump_151 =>
                apply False.elim assump_151
        let assump_140 := assump_1 assump_172
        let assump_156 := And.left assump_140
        have assump_173 : (False → p7) := by
          intro assump_158
          apply False.elim assump_158
        let assump_157 := assump_156 assump_173
        apply False.elim assump_157
    case inr assump_129 =>
      apply False.elim assump_129


variable (p2 p0 p3 p4 : Prop)
theorem file91_87280 : ((((((p3 ∧ p4) → False) → False) ∧ (((p2 → False) ∧ (p0 ∨ False)) → False)) ∧ ((((p2 ∨ True) ∨ (p0 → False)) ∨ ((p2 ∨ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : (((p2 ∨ True) ∨ (p0 → False)) ∨ ((p2 ∨ p0) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p5 p3 p2 p1 p7 p6 p0 : Prop)
theorem file91_87868 : (((((True ∨ p3) ∨ (p3 → False)) → False) → False) → ((((p6 ∧ p3) ∧ (p5 ∨ p5)) → ((p0 → True) ∨ (p5 ∧ p0))) ∨ (((p1 ∨ p2) ∨ (True → False)) ∧ ((False ∨ p1) ∨ (p5 → p7))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        apply Or.inl
        intro assump_17
        apply True.intro
      case inr assump_14 =>
        apply Or.inl
        intro assump_20
        apply True.intro


variable (p7 p0 : Prop)
theorem file91_88465 : ((((((False → p0) ∨ (p0 ∨ False)) → False) → (((p7 ∧ False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → p0) ∨ (p0 ∨ False)) → False) → (((p7 ∧ False) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_22 : ((False → p0) ∨ (p0 ∨ False)) := by
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_22
    apply False.elim assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p2 p6 p3 p7 p5 p4 p0 p1 : Prop)
theorem file91_89058 : (((((p7 ∧ p3) → (p3 → p0)) ∧ ((p2 ∨ p4) ∧ (True → False))) → False) ∨ ((((p2 ∧ p7) ∨ (p0 ∧ p4)) ∨ ((p6 → p2) ∨ (p5 → False))) ∨ (((p1 ∧ p6) ∧ (p7 → False)) → ((False → p1) ∨ (p5 ∧ p1))))) := by
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


variable (p1 p5 p4 p2 p6 p0 p7 : Prop)
theorem file91_89812 : (((((p5 → p4) ∧ (True ∨ True)) ∨ ((p0 ∧ p1) → False)) ∧ (((p2 ∧ p2) ∨ (p5 → p5)) ∨ ((p6 → False) ∧ (True ∧ p0)))) → ((((p7 ∨ p7) → (False → False)) → ((True → p4) ∧ (p5 → True))) → (((p6 → False) → (p2 ∨ p0)) → ((False ∧ False) → (p0 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p5 p0 p1 p3 p2 : Prop)
theorem file91_90288 : (((((p1 → p2) ∨ (p5 → p0)) ∨ ((p3 → p1) → (p1 ∨ p1))) ∧ (((p5 → p3) → False) ∧ ((True ∨ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_44 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_16 := assump_11 assump_44
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_3
        case intro assump_22 assump_23 =>
          have assump_45 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_28 := assump_23 assump_45
          apply False.elim assump_28
    case inr assump_5 =>
      cases assump_3
      case intro assump_34 assump_35 =>
        have assump_46 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_40 := assump_35 assump_46
        apply False.elim assump_40


variable (p3 p7 p6 p0 p5 p4 : Prop)
theorem file91_91408 : ((((((p7 → True) → False) → False) ∨ (((p4 ∧ p5) ∨ (p6 ∨ p3)) ∨ ((p0 ∨ p3) ∧ (p5 → p5)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 → True) → False) → False) ∨ (((p4 ∧ p5) ∨ (p6 ∨ p3)) ∨ ((p0 ∨ p3) ∧ (p5 → p5)))) := by
    apply Or.inl
    intro assump_5
    have assump_17 : (p7 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p7 : Prop)
theorem file91_91953 : ((((((False ∧ p2) ∨ (p7 → False)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_28 : ((((False ∧ p2) ∨ (p7 → False)) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
      case inr assump_9 =>
        have assump_29 : (False → False) := by
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_7 assump_29
        apply False.elim assump_18
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p5 p3 p0 p4 : Prop)
theorem file91_92720 : ((((((p4 ∨ p4) ∨ (p4 → False)) → False) → (((False ∨ p5) → (p3 → False)) ∨ ((p5 → p5) → (p4 ∨ True)))) → ((((False → False) ∨ (p5 ∧ p5)) ∨ ((p3 → p0) ∨ (p4 ∧ p4))) → False)) → False) := by
  intro assump_31
  have assump_71 : ((((p4 ∨ p4) ∨ (p4 → False)) → False) → (((False ∨ p5) → (p3 → False)) ∨ ((p5 → p5) → (p4 ∨ True)))) := by
    intro assump_35
    apply Or.inl
    intro assump_38
    intro assump_39
    cases assump_38
    case inl assump_42 =>
      apply False.elim assump_42
    case inr assump_43 =>
      have assump_72 : ((p4 ∨ p4) ∨ (p4 → False)) := by
        apply Or.inr
        intro assump_51
        have assump_73 : ((p4 ∨ p4) ∨ (p4 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_51
        let assump_57 := assump_35 assump_73
        apply False.elim assump_57
      let assump_50 := assump_35 assump_72
      apply False.elim assump_50
  let assump_34 := assump_31 assump_71
  have assump_74 : (((False → False) ∨ (p5 ∧ p5)) ∨ ((p3 → p0) ∨ (p4 ∧ p4))) := by
    apply Or.inl
    apply Or.inl
    intro assump_65
    apply False.elim assump_65
  let assump_64 := assump_34 assump_74
  apply False.elim assump_64


variable (p1 p4 p0 p5 p7 p3 p2 : Prop)
theorem file91_93960 : (((((p5 ∧ False) → False) ∨ ((p3 → False) → (p2 → False))) → False) → ((((True ∨ p0) → (True → p4)) → ((p7 → False) ∧ (p1 → p2))) ∧ (((p7 ∧ p0) → (False ∧ True)) ∨ ((p0 → False) → False)))) := by
  intro assump_11
  apply And.intro
  intro assump_12
  apply And.intro
  intro assump_13
  have assump_71 : (((p5 ∧ False) → False) ∨ ((p3 → False) → (p2 → False))) := by
    apply Or.inl
    intro assump_21
    cases assump_21
    case intro assump_22 assump_23 =>
      apply False.elim assump_23
  let assump_20 := assump_11 assump_71
  apply False.elim assump_20
  intro assump_31
  have assump_72 : (((p5 ∧ False) → False) ∨ ((p3 → False) → (p2 → False))) := by
    apply Or.inl
    intro assump_39
    cases assump_39
    case intro assump_40 assump_41 =>
      apply False.elim assump_41
  let assump_38 := assump_11 assump_72
  apply False.elim assump_38
  apply Or.inl
  intro assump_51
  apply And.intro
  cases assump_51
  case intro assump_52 assump_53 =>
    have assump_73 : (((p5 ∧ False) → False) ∨ ((p3 → False) → (p2 → False))) := by
      apply Or.inl
      intro assump_61
      cases assump_61
      case intro assump_62 assump_63 =>
        apply False.elim assump_63
    let assump_60 := assump_11 assump_73
    apply False.elim assump_60
  apply True.intro


variable (p2 p5 p1 p3 : Prop)
theorem file91_95292 : ((((((p1 ∨ p2) ∨ (p5 → True)) → False) → (((p3 → p3) → False) → False)) → False) → False) := by
  intro assump_5
  have assump_23 : ((((p1 ∨ p2) ∨ (p5 → True)) → False) → (((p3 → p3) → False) → False)) := by
    intro assump_9
    intro assump_10
    have assump_24 : ((p1 ∨ p2) ∨ (p5 → True)) := by
      apply Or.inr
      intro assump_16
      apply True.intro
    let assump_15 := assump_9 assump_24
    apply False.elim assump_15
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p1 p7 p3 p2 p4 p6 p0 : Prop)
theorem file91_95855 : (((((p6 ∧ p3) ∨ (p7 → False)) → ((p4 ∨ p4) → (p1 → True))) → False) → ((((p7 ∨ p0) → (True → False)) ∧ ((p7 ∧ p3) ∨ (p6 ∨ p7))) ∨ (((p3 ∨ p1) ∨ (p2 ∧ p7)) ∧ ((p4 → False) → (False ∧ p3))))) := by
  intro assump_1
  have assump_37 : (((p6 ∧ p3) ∨ (p7 → False)) → ((p4 ∨ p4) → (p1 → True))) := by
    intro assump_31
    intro assump_32
    intro assump_33
    apply True.intro
  let assump_30 := assump_1 assump_37
  apply False.elim assump_30


variable (p4 p0 p6 p3 p2 p5 p7 : Prop)
theorem file91_96361 : (((((p4 → p0) ∨ (p5 ∨ p3)) → False) → (((p5 ∧ p5) ∧ (p6 ∨ p3)) → ((p2 → False) → (p7 ∨ True)))) ∨ ((((True → p0) ∧ (False ∨ p7)) ∧ ((p2 ∧ p6) ∧ (p7 ∨ p4))) ∧ (((True ∧ True) ∨ (False → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case inl assump_14 =>
        apply Or.inr
        apply True.intro
      case inr assump_15 =>
        apply Or.inr
        apply True.intro


variable (p4 p3 p1 p6 p5 p0 : Prop)
theorem file91_96972 : ((((((p3 ∧ p0) ∧ (False ∨ p0)) ∨ ((p4 → False) ∧ (True ∧ True))) → (((False ∨ p0) → False) → False)) ∧ ((((False ∧ True) → False) ∧ ((False → p1) → (p5 ∧ p4))) ∧ (((False ∧ p5) → (p6 → False)) → False))) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        have assump_51 : ((False ∧ p5) → (p6 → False)) := by
          intro assump_40
          intro assump_41
          cases assump_40
          case intro assump_44 assump_45 =>
            apply False.elim assump_44
        let assump_39 := assump_30 assump_51
        apply False.elim assump_39


variable (p0 p5 p3 : Prop)
theorem file91_97736 : (((((True → False) ∧ (p0 ∨ p5)) ∧ ((False ∧ False) ∨ (p3 → False))) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_5
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
          case inr assump_15 =>
            have assump_58 : ((True → False) → False) := by
              intro assump_25
              have assump_59 : True := by
                apply True.intro
              let assump_28 := assump_25 assump_59
              apply False.elim assump_28
            let assump_24 := assump_3 assump_58
            apply False.elim assump_24
        case inr assump_11 =>
          cases assump_5
          case inl assump_37 =>
            cases assump_37
            case intro assump_39 assump_40 =>
              apply False.elim assump_39
          case inr assump_38 =>
            have assump_60 : ((True → False) → False) := by
              intro assump_48
              have assump_61 : True := by
                apply True.intro
              let assump_51 := assump_48 assump_61
              apply False.elim assump_51
            let assump_47 := assump_3 assump_60
            apply False.elim assump_47


