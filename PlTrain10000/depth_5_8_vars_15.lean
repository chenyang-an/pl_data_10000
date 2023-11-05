variable (p3 p6 p4 p2 : Prop)
theorem file15_38 : (((((p3 → False) → False) → False) → False) → ((((p6 → False) ∧ (p4 → p6)) ∧ ((False ∧ False) ∧ (p6 ∧ p2))) → False)) := by
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
          apply False.elim assump_13


variable (p2 p6 p1 p4 p3 p5 p0 p7 : Prop)
theorem file15_532 : (((((p2 → p2) ∧ (False → False)) → False) → (((p6 ∨ p0) → (p7 → False)) ∧ ((p0 ∨ p7) → False))) ∨ ((((p1 ∧ True) → (p0 ∨ p3)) → ((p0 ∨ p0) → False)) ∧ (((p0 ∧ False) ∨ (p4 ∨ p3)) ∨ ((p1 → False) ∧ (p5 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_67 : ((p2 → p2) ∧ (False → False)) := by
      apply And.intro
      intro assump_13
      exact assump_13
      intro assump_16
      apply False.elim assump_16
    let assump_12 := assump_1 assump_67
    apply False.elim assump_12
  case inr assump_7 =>
    have assump_68 : ((p2 → p2) ∧ (False → False)) := by
      apply And.intro
      intro assump_27
      exact assump_27
      intro assump_30
      apply False.elim assump_30
    let assump_26 := assump_1 assump_68
    apply False.elim assump_26
  intro assump_36
  cases assump_36
  case inl assump_37 =>
    have assump_69 : ((p2 → p2) ∧ (False → False)) := by
      apply And.intro
      intro assump_44
      exact assump_44
      intro assump_47
      apply False.elim assump_47
    let assump_43 := assump_1 assump_69
    apply False.elim assump_43
  case inr assump_38 =>
    have assump_70 : ((p2 → p2) ∧ (False → False)) := by
      apply And.intro
      intro assump_58
      exact assump_58
      intro assump_61
      apply False.elim assump_61
    let assump_57 := assump_1 assump_70
    apply False.elim assump_57


variable (p2 p3 p1 p0 p7 : Prop)
theorem file15_2033 : ((((((True ∨ p1) ∧ (True → True)) ∧ ((p2 → p0) → False)) → (((p3 ∨ p2) ∧ (p0 ∧ p7)) → ((False ∨ p1) ∧ (True ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_136 : ((((True ∨ p1) ∧ (True → True)) ∧ ((p2 → p0) → False)) → (((p3 ∨ p2) ∧ (p0 ∧ p7)) → ((False ∨ p1) ∧ (True ∧ p0)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_5
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                have assump_137 : (p2 → p0) := by
                  intro assump_32
                  exact assump_13
                let assump_31 := assump_20 assump_137
                apply False.elim assump_31
              case inr assump_24 =>
                apply Or.inr
                exact assump_24
      case inr assump_10 =>
        cases assump_8
        case intro assump_46 assump_47 =>
          cases assump_5
          case intro assump_52 assump_53 =>
            cases assump_52
            case intro assump_54 assump_55 =>
              cases assump_54
              case inl assump_56 =>
                have assump_138 : (p2 → p0) := by
                  intro assump_65
                  exact assump_46
                let assump_64 := assump_53 assump_138
                apply False.elim assump_64
              case inr assump_57 =>
                apply Or.inr
                exact assump_57
    apply And.intro
    apply True.intro
    cases assump_6
    case intro assump_77 assump_78 =>
      cases assump_77
      case inl assump_79 =>
        cases assump_78
        case intro assump_83 assump_84 =>
          cases assump_5
          case intro assump_89 assump_90 =>
            cases assump_89
            case intro assump_91 assump_92 =>
              cases assump_91
              case inl assump_93 =>
                exact assump_83
              case inr assump_94 =>
                exact assump_83
      case inr assump_80 =>
        cases assump_78
        case intro assump_109 assump_110 =>
          cases assump_5
          case intro assump_115 assump_116 =>
            cases assump_115
            case intro assump_117 assump_118 =>
              cases assump_117
              case inl assump_119 =>
                exact assump_109
              case inr assump_120 =>
                exact assump_109
  let assump_4 := assump_1 assump_136
  apply False.elim assump_4


variable (p7 p0 p3 p6 p5 : Prop)
theorem file15_4754 : (((((False ∨ p0) ∨ (p7 → True)) ∨ ((False → p7) ∨ (p3 ∨ p0))) ∨ (((p0 ∧ p7) ∨ (p6 → False)) ∨ ((p6 ∧ p7) ∧ (p7 ∧ p5)))) ∨ ((((p3 ∨ p6) → False) → ((True → p7) ∧ (p3 ∧ p7))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply True.intro


variable (p7 p2 p6 p0 p3 p5 p4 : Prop)
theorem file15_5102 : (((((p6 ∧ p4) ∨ (p0 ∧ p4)) ∧ ((p2 → p0) → False)) ∧ (((p5 ∧ p3) ∨ (p4 ∨ p0)) → False)) → ((((p3 ∨ p6) → (p6 ∨ p3)) → ((p2 ∧ p3) → (p0 → False))) → (((p3 ∨ True) → (p7 → True)) ∧ ((p4 → False) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  apply True.intro
  cases assump_1
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply Or.inl
          intro assump_23
          have assump_49 : ((p5 ∧ p3) ∨ (p4 ∨ p0)) := by
            apply Or.inr
            apply Or.inl
            exact assump_23
          let assump_27 := assump_8 assump_49
          apply False.elim assump_27
      case inr assump_12 =>
        cases assump_12
        case intro assump_31 assump_32 =>
          apply Or.inl
          intro assump_41
          have assump_50 : ((p5 ∧ p3) ∨ (p4 ∨ p0)) := by
            apply Or.inr
            apply Or.inl
            exact assump_41
          let assump_45 := assump_8 assump_50
          apply False.elim assump_45


variable (p5 p3 p7 p0 p6 p4 p1 : Prop)
theorem file15_6339 : (((((p6 ∨ True) → False) ∧ ((p4 ∧ p0) ∨ (p7 → p4))) ∧ (((False ∧ p6) → (True ∨ False)) → False)) → ((((p7 ∧ False) → (p5 → False)) ∧ ((False → p0) → (True → p1))) ∧ (((p3 → p1) → (True → p0)) ∨ ((True ∧ p6) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7
  intro assump_12
  intro assump_13
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_21
      case inl assump_24 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          have assump_98 : ((False ∧ p6) → (True ∨ False)) := by
            intro assump_35
            cases assump_35
            case intro assump_36 assump_37 =>
              apply False.elim assump_36
          let assump_34 := assump_19 assump_98
          apply False.elim assump_34
      case inr assump_25 =>
        have assump_99 : ((False ∧ p6) → (True ∨ False)) := by
          intro assump_48
          cases assump_48
          case intro assump_49 assump_50 =>
            apply False.elim assump_49
        let assump_47 := assump_19 assump_99
        apply False.elim assump_47
  cases assump_1
  case intro assump_56 assump_57 =>
    cases assump_56
    case intro assump_58 assump_59 =>
      cases assump_59
      case inl assump_62 =>
        cases assump_62
        case intro assump_64 assump_65 =>
          apply Or.inl
          intro assump_72
          intro assump_73
          exact assump_65
      case inr assump_63 =>
        apply Or.inl
        intro assump_82
        intro assump_83
        have assump_100 : ((False ∧ p6) → (True ∨ False)) := by
          intro assump_90
          cases assump_90
          case intro assump_91 assump_92 =>
            apply False.elim assump_91
        let assump_89 := assump_57 assump_100
        apply False.elim assump_89


variable (p7 p0 p1 p6 p5 p2 : Prop)
theorem file15_8358 : ((((((p7 ∧ False) ∧ (False → False)) ∧ ((True → p5) → (p0 → p1))) ∧ (((p7 ∨ p1) ∨ (False → True)) ∨ ((p2 ∨ p2) → (p5 → False)))) ∧ ((((p7 ∧ p6) → (p2 → False)) ∨ ((p0 ∨ True) → (p0 ∧ True))) → False)) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            apply False.elim assump_34


variable (p1 p5 p2 p0 p4 p3 : Prop)
theorem file15_9001 : (((((p5 → p1) → (p3 → False)) ∧ ((p4 ∧ p5) ∧ (p0 → p2))) ∧ (((True → False) ∧ (p4 → p0)) ∧ ((p4 → p4) → False))) → ((((p5 → False) ∧ (False → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_6
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              have assump_38 : (p4 → p4) := by
                intro assump_32
                exact assump_32
              let assump_31 := assump_22 assump_38
              apply False.elim assump_31


variable (p5 p3 p6 p2 p4 p1 : Prop)
theorem file15_9849 : (((((True ∨ p2) → False) ∨ ((p3 → False) ∧ (p2 → False))) → (((True → False) ∨ (p3 ∧ p4)) → ((p6 → p3) → (p1 → False)))) ∨ ((((p5 ∧ p6) ∨ (p4 → p6)) ∧ ((p4 ∨ p6) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_1
    case inl assump_13 =>
      have assump_58 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_17 := assump_13 assump_58
      apply False.elim assump_17
    case inr assump_14 =>
      cases assump_14
      case intro assump_21 assump_22 =>
        have assump_59 : True := by
          apply True.intro
        let assump_29 := assump_9 assump_59
        apply False.elim assump_29
  case inr assump_10 =>
    cases assump_10
    case intro assump_33 assump_34 =>
      cases assump_1
      case inl assump_39 =>
        have assump_60 : (True ∨ p2) := by
          apply Or.inl
          apply True.intro
        let assump_43 := assump_39 assump_60
        apply False.elim assump_43
      case inr assump_40 =>
        cases assump_40
        case intro assump_47 assump_48 =>
          have assump_61 : p3 := by
            exact assump_33
          let assump_54 := assump_47 assump_61
          apply False.elim assump_54


variable (p4 p0 p7 p2 p3 p1 p5 : Prop)
theorem file15_11207 : (((((p2 → p2) ∧ (p5 ∨ p3)) ∨ ((p7 ∨ p7) ∨ (p4 ∧ p0))) ∧ (((p5 ∧ False) → False) → False)) → ((((p1 ∨ p4) ∨ (True → p5)) → False) → (((p7 ∨ p2) → False) ∨ ((False → p7) → (p4 ∨ p0))))) := by
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    cases assump_14
    case inl assump_16 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_19
        case inl assump_22 =>
          apply Or.inl
          intro assump_28
          cases assump_28
          case inl assump_29 =>
            have assump_207 : ((p5 ∧ False) → False) := by
              intro assump_35
              cases assump_35
              case intro assump_36 assump_37 =>
                apply False.elim assump_37
            let assump_34 := assump_15 assump_207
            apply False.elim assump_34
          case inr assump_30 =>
            have assump_208 : ((p5 ∧ False) → False) := by
              intro assump_49
              cases assump_49
              case intro assump_50 assump_51 =>
                apply False.elim assump_51
            let assump_48 := assump_15 assump_208
            apply False.elim assump_48
        case inr assump_23 =>
          apply Or.inl
          intro assump_63
          cases assump_63
          case inl assump_64 =>
            have assump_209 : ((p5 ∧ False) → False) := by
              intro assump_70
              cases assump_70
              case intro assump_71 assump_72 =>
                apply False.elim assump_72
            let assump_69 := assump_15 assump_209
            apply False.elim assump_69
          case inr assump_65 =>
            have assump_210 : ((p5 ∧ False) → False) := by
              intro assump_84
              cases assump_84
              case intro assump_85 assump_86 =>
                apply False.elim assump_86
            let assump_83 := assump_15 assump_210
            apply False.elim assump_83
    case inr assump_17 =>
      cases assump_17
      case inl assump_94 =>
        cases assump_94
        case inl assump_96 =>
          apply Or.inl
          intro assump_102
          cases assump_102
          case inl assump_103 =>
            have assump_211 : ((p5 ∧ False) → False) := by
              intro assump_109
              cases assump_109
              case intro assump_110 assump_111 =>
                apply False.elim assump_111
            let assump_108 := assump_15 assump_211
            apply False.elim assump_108
          case inr assump_104 =>
            have assump_212 : ((p5 ∧ False) → False) := by
              intro assump_123
              cases assump_123
              case intro assump_124 assump_125 =>
                apply False.elim assump_125
            let assump_122 := assump_15 assump_212
            apply False.elim assump_122
        case inr assump_97 =>
          apply Or.inl
          intro assump_137
          cases assump_137
          case inl assump_138 =>
            have assump_213 : ((p5 ∧ False) → False) := by
              intro assump_144
              cases assump_144
              case intro assump_145 assump_146 =>
                apply False.elim assump_146
            let assump_143 := assump_15 assump_213
            apply False.elim assump_143
          case inr assump_139 =>
            have assump_214 : ((p5 ∧ False) → False) := by
              intro assump_158
              cases assump_158
              case intro assump_159 assump_160 =>
                apply False.elim assump_160
            let assump_157 := assump_15 assump_214
            apply False.elim assump_157
      case inr assump_95 =>
        cases assump_95
        case intro assump_168 assump_169 =>
          apply Or.inl
          intro assump_176
          cases assump_176
          case inl assump_177 =>
            have assump_215 : ((p5 ∧ False) → False) := by
              intro assump_183
              cases assump_183
              case intro assump_184 assump_185 =>
                apply False.elim assump_185
            let assump_182 := assump_15 assump_215
            apply False.elim assump_182
          case inr assump_178 =>
            have assump_216 : ((p5 ∧ False) → False) := by
              intro assump_197
              cases assump_197
              case intro assump_198 assump_199 =>
                apply False.elim assump_199
            let assump_196 := assump_15 assump_216
            apply False.elim assump_196


variable (p4 p5 p1 p7 p2 : Prop)
theorem file15_15731 : ((((((p7 → False) → False) → False) ∧ (((p4 → p4) ∨ (False ∨ p5)) ∧ ((p5 ∧ False) ∧ (p2 ∨ p5)))) ∧ ((((p1 ∨ p5) ∧ (p2 ∨ True)) → False) → False)) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
        case inr assump_11 =>
          cases assump_11
          case inl assump_22 =>
            apply False.elim assump_22
          case inr assump_23 =>
            cases assump_9
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                apply False.elim assump_31


variable (p6 : Prop)
theorem file15_16709 : ((((((False ∧ p6) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p6) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ p6) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p3 p1 p4 p7 : Prop)
theorem file15_17237 : ((((((p4 → False) ∧ (p7 ∨ p7)) → ((p1 ∨ p7) ∧ (p7 ∨ p3))) ∨ (((True → False) ∨ (p1 ∨ p3)) ∨ ((p4 → p3) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p4 → False) ∧ (p7 ∨ p7)) → ((p1 ∨ p7) ∧ (p7 ∨ p3))) ∨ (((True → False) ∨ (p1 ∨ p3)) ∨ ((p4 → p3) → False))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inr
        exact assump_10
      case inr assump_11 =>
        apply Or.inr
        exact assump_11
    cases assump_5
    case intro assump_16 assump_17 =>
      cases assump_17
      case inl assump_20 =>
        apply Or.inl
        exact assump_20
      case inr assump_21 =>
        apply Or.inl
        exact assump_21
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p3 p0 p1 : Prop)
theorem file15_18151 : ((((((p3 → p7) ∨ (p1 → False)) ∧ ((p0 → p0) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p3 → p7) ∨ (p1 → False)) ∧ ((p0 → p0) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_36 : (p0 → p0) := by
          intro assump_15
          exact assump_15
        let assump_14 := assump_7 assump_36
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_37 : (p0 → p0) := by
          intro assump_26
          exact assump_26
        let assump_25 := assump_7 assump_37
        apply False.elim assump_25
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p3 p6 p4 p5 p1 p7 p2 p0 : Prop)
theorem file15_18965 : (((((p5 → p3) ∧ (p2 ∨ p4)) → ((p2 ∧ p4) ∨ (p4 → False))) ∧ (((p5 → False) → (p6 ∨ p2)) → False)) → ((((p1 → p5) ∨ (p7 ∨ p1)) → ((p2 ∨ p3) ∨ (p2 → p5))) ∨ (((p0 → False) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      apply Or.inr
      intro assump_13
      have assump_55 : ((p5 → False) → (p6 ∨ p2)) := by
        intro assump_19
        apply Or.inr
        exact assump_13
      let assump_18 := assump_3 assump_55
      apply False.elim assump_18
    case inr assump_10 =>
      cases assump_10
      case inl assump_25 =>
        apply Or.inr
        intro assump_29
        have assump_56 : ((p5 → False) → (p6 ∨ p2)) := by
          intro assump_35
          apply Or.inr
          exact assump_29
        let assump_34 := assump_3 assump_56
        apply False.elim assump_34
      case inr assump_26 =>
        apply Or.inr
        intro assump_43
        have assump_57 : ((p5 → False) → (p6 ∨ p2)) := by
          intro assump_49
          apply Or.inr
          exact assump_43
        let assump_48 := assump_3 assump_57
        apply False.elim assump_48


variable (p3 p4 p0 p1 p2 p7 : Prop)
theorem file15_20227 : (((((True → False) ∧ (p2 ∧ p3)) ∨ ((p3 ∨ p0) ∧ (False ∧ p3))) ∧ (((False → p4) ∧ (p0 ∨ p1)) ∨ ((p1 → p3) → (p7 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                have assump_73 : True := by
                  apply True.intro
                let assump_30 := assump_6 assump_73
                apply False.elim assump_30
              case inr assump_23 =>
                have assump_74 : True := by
                  apply True.intro
                let assump_40 := assump_6 assump_74
                apply False.elim assump_40
          case inr assump_17 =>
            have assump_75 : True := by
              apply True.intro
            let assump_53 := assump_6 assump_75
            apply False.elim assump_53
    case inr assump_5 =>
      cases assump_5
      case intro assump_57 assump_58 =>
        cases assump_57
        case inl assump_59 =>
          cases assump_58
          case intro assump_63 assump_64 =>
            apply False.elim assump_63
        case inr assump_60 =>
          cases assump_58
          case intro assump_69 assump_70 =>
            apply False.elim assump_69


variable (p5 : Prop)
theorem file15_21805 : ((((((p5 → False) → (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p5 → False) → (False → False)) → False) → False) := by
    intro assump_5
    have assump_20 : ((p5 → False) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p5 p1 p4 p7 p0 p3 : Prop)
theorem file15_22331 : ((((((p0 ∧ p6) ∨ (p1 ∧ p5)) ∨ ((p0 ∧ p7) ∨ (p5 ∧ True))) ∨ (((p4 ∧ p5) → (p1 ∧ p1)) ∨ ((p4 → False) → (p0 ∧ p0)))) ∧ ((((p0 → p3) → (p1 → False)) ∧ ((p5 ∧ p4) ∧ (p1 ∧ p3))) ∧ (((False ∧ p6) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_19
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    cases assump_23
                    case intro assump_30 assump_31 =>
                      have assump_228 : ((False ∧ p6) → False) := by
                        intro assump_39
                        cases assump_39
                        case intro assump_40 assump_41 =>
                          apply False.elim assump_40
                      let assump_38 := assump_17 assump_228
                      apply False.elim assump_38
        case inr assump_9 =>
          cases assump_9
          case intro assump_47 assump_48 =>
            cases assump_3
            case intro assump_53 assump_54 =>
              cases assump_53
              case intro assump_55 assump_56 =>
                cases assump_56
                case intro assump_59 assump_60 =>
                  cases assump_59
                  case intro assump_61 assump_62 =>
                    cases assump_60
                    case intro assump_67 assump_68 =>
                      have assump_229 : ((False ∧ p6) → False) := by
                        intro assump_76
                        cases assump_76
                        case intro assump_77 assump_78 =>
                          apply False.elim assump_77
                      let assump_75 := assump_54 assump_229
                      apply False.elim assump_75
      case inr assump_7 =>
        cases assump_7
        case inl assump_84 =>
          cases assump_84
          case intro assump_86 assump_87 =>
            cases assump_3
            case intro assump_92 assump_93 =>
              cases assump_92
              case intro assump_94 assump_95 =>
                cases assump_95
                case intro assump_98 assump_99 =>
                  cases assump_98
                  case intro assump_100 assump_101 =>
                    cases assump_99
                    case intro assump_106 assump_107 =>
                      have assump_230 : ((False ∧ p6) → False) := by
                        intro assump_115
                        cases assump_115
                        case intro assump_116 assump_117 =>
                          apply False.elim assump_116
                      let assump_114 := assump_93 assump_230
                      apply False.elim assump_114
        case inr assump_85 =>
          cases assump_85
          case intro assump_123 assump_124 =>
            cases assump_3
            case intro assump_129 assump_130 =>
              cases assump_129
              case intro assump_131 assump_132 =>
                cases assump_132
                case intro assump_135 assump_136 =>
                  cases assump_135
                  case intro assump_137 assump_138 =>
                    cases assump_136
                    case intro assump_143 assump_144 =>
                      have assump_231 : ((False ∧ p6) → False) := by
                        intro assump_152
                        cases assump_152
                        case intro assump_153 assump_154 =>
                          apply False.elim assump_153
                      let assump_151 := assump_130 assump_231
                      apply False.elim assump_151
    case inr assump_5 =>
      cases assump_5
      case inl assump_160 =>
        cases assump_3
        case intro assump_164 assump_165 =>
          cases assump_164
          case intro assump_166 assump_167 =>
            cases assump_167
            case intro assump_170 assump_171 =>
              cases assump_170
              case intro assump_172 assump_173 =>
                cases assump_171
                case intro assump_178 assump_179 =>
                  have assump_232 : ((False ∧ p6) → False) := by
                    intro assump_187
                    cases assump_187
                    case intro assump_188 assump_189 =>
                      apply False.elim assump_188
                  let assump_186 := assump_165 assump_232
                  apply False.elim assump_186
      case inr assump_161 =>
        cases assump_3
        case intro assump_197 assump_198 =>
          cases assump_197
          case intro assump_199 assump_200 =>
            cases assump_200
            case intro assump_203 assump_204 =>
              cases assump_203
              case intro assump_205 assump_206 =>
                cases assump_204
                case intro assump_211 assump_212 =>
                  have assump_233 : ((False ∧ p6) → False) := by
                    intro assump_220
                    cases assump_220
                    case intro assump_221 assump_222 =>
                      apply False.elim assump_221
                  let assump_219 := assump_198 assump_233
                  apply False.elim assump_219


variable (p3 p6 p1 p7 p4 p0 p5 : Prop)
theorem file15_27963 : (((((False → False) ∨ (p4 ∨ p1)) → False) → (((True → False) → False) ∧ ((p5 → p3) ∨ (p6 → p7)))) ∨ ((((True → False) ∨ (p5 → False)) → ((p0 → False) ∧ (p1 → False))) → (((p3 → False) → False) ∨ ((p1 ∨ p5) ∨ (p4 ∧ p6))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_27 : ((False → False) ∨ (p4 ∨ p1)) := by
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_27
  apply False.elim assump_7
  apply Or.inl
  intro assump_16
  have assump_28 : ((False → False) ∨ (p4 ∨ p1)) := by
    apply Or.inl
    intro assump_21
    apply False.elim assump_21
  let assump_20 := assump_1 assump_28
  apply False.elim assump_20


variable (p4 p3 p1 p2 : Prop)
theorem file15_28721 : (((((False → False) → False) → False) → False) → ((((False → False) ∨ (p1 ∨ p4)) ∧ ((p1 → False) → False)) ∧ (((True → False) → (True ∨ True)) → ((True ∧ p3) ∧ (True → p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  have assump_66 : (((False → False) → False) → False) := by
    intro assump_13
    have assump_67 : (False → False) := by
      intro assump_17
      apply False.elim assump_17
    let assump_16 := assump_13 assump_67
    apply False.elim assump_16
  let assump_12 := assump_1 assump_66
  apply False.elim assump_12
  intro assump_26
  apply And.intro
  apply And.intro
  apply True.intro
  have assump_68 : (((False → False) → False) → False) := by
    intro assump_32
    have assump_69 : (False → False) := by
      intro assump_36
      apply False.elim assump_36
    let assump_35 := assump_32 assump_69
    apply False.elim assump_35
  let assump_31 := assump_1 assump_68
  apply False.elim assump_31
  intro assump_45
  have assump_70 : (((False → False) → False) → False) := by
    intro assump_53
    have assump_71 : (False → False) := by
      intro assump_57
      apply False.elim assump_57
    let assump_56 := assump_53 assump_71
    apply False.elim assump_56
  let assump_52 := assump_1 assump_70
  apply False.elim assump_52


variable (p0 p1 p7 p2 p3 : Prop)
theorem file15_30135 : ((((((p2 ∨ p2) ∨ (p2 → p0)) ∨ ((True → False) ∨ (p7 → p2))) ∨ (((False → False) → (p1 ∨ p3)) ∨ ((p3 → True) → False))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p2 ∨ p2) ∨ (p2 → p0)) ∨ ((True → False) ∨ (p7 → p2))) ∨ (((False → False) → (p1 ∨ p3)) ∨ ((p3 → True) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : ((((p2 ∨ p2) ∨ (p2 → p0)) ∨ ((True → False) ∨ (p7 → p2))) ∨ (((False → False) → (p1 ∨ p3)) ∨ ((p3 → True) → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p7 p5 p6 : Prop)
theorem file15_30936 : ((((((True ∨ p0) → False) → ((p7 ∨ True) → False)) ∧ (((p6 ∧ p6) ∧ (False ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_41 : ((((True ∨ p0) → False) → ((p7 ∨ True) → False)) ∧ (((p6 ∧ p6) ∧ (False ∧ p5)) → False)) := by
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_42 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_5 assump_42
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_43 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_21 := assump_5 assump_43
      apply False.elim assump_21
    intro assump_25
    cases assump_25
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_27
        case intro assump_34 assump_35 =>
          apply False.elim assump_34
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p3 p4 p7 p5 p0 p2 : Prop)
theorem file15_32001 : (((((False ∧ p7) ∨ (p4 ∨ p0)) → False) ∧ (((p2 ∧ p5) ∨ (False → p2)) ∧ ((p3 ∧ p5) ∧ (p4 ∧ p5)))) → False) := by
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
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                have assump_65 : ((False ∧ p7) ∨ (p4 ∨ p0)) := by
                  apply Or.inr
                  apply Or.inl
                  exact assump_24
                let assump_36 := assump_2 assump_65
                apply False.elim assump_36
      case inr assump_9 =>
        cases assump_7
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            cases assump_43
            case intro assump_50 assump_51 =>
              have assump_66 : ((False ∧ p7) ∨ (p4 ∨ p0)) := by
                apply Or.inr
                apply Or.inl
                exact assump_50
              let assump_61 := assump_2 assump_66
              apply False.elim assump_61


variable (p6 p0 p3 p1 p5 p4 p2 : Prop)
theorem file15_33371 : ((((((p5 ∧ p0) ∧ (p0 → False)) ∧ ((p3 ∧ p4) ∧ (p6 → False))) ∨ (((p0 ∨ p0) → False) → False)) ∧ ((((False → p4) → False) → ((p2 ∨ False) ∧ (p1 → False))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                have assump_90 : (((False → p4) → False) → ((p2 ∨ False) ∧ (p1 → False))) := by
                  intro assump_35
                  apply And.intro
                  have assump_91 : (False → p4) := by
                    intro assump_39
                    apply False.elim assump_39
                  let assump_38 := assump_35 assump_91
                  apply False.elim assump_38
                  intro assump_45
                  have assump_92 : (False → p4) := by
                    intro assump_51
                    apply False.elim assump_51
                  let assump_50 := assump_35 assump_92
                  apply False.elim assump_50
                let assump_34 := assump_7 assump_90
                apply False.elim assump_34
    case inr assump_9 =>
      have assump_93 : (((False → p4) → False) → ((p2 ∨ False) ∧ (p1 → False))) := by
        intro assump_65
        apply And.intro
        have assump_94 : (False → p4) := by
          intro assump_69
          apply False.elim assump_69
        let assump_68 := assump_65 assump_94
        apply False.elim assump_68
        intro assump_75
        have assump_95 : (False → p4) := by
          intro assump_81
          apply False.elim assump_81
        let assump_80 := assump_65 assump_95
        apply False.elim assump_80
      let assump_64 := assump_7 assump_93
      apply False.elim assump_64


variable (p3 p0 p6 p2 p1 : Prop)
theorem file15_35467 : ((((((p6 ∧ p6) ∨ (p6 → False)) ∨ ((p1 ∧ p2) → False)) ∨ (((p6 ∨ p3) → False) ∧ ((p0 → p2) ∧ (p2 → p0)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p6 ∧ p6) ∨ (p6 → False)) ∨ ((p1 ∧ p2) → False)) ∨ (((p6 ∨ p3) → False) ∧ ((p0 → p2) ∧ (p2 → p0)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : ((((p6 ∧ p6) ∨ (p6 → False)) ∨ ((p1 ∧ p2) → False)) ∨ (((p6 ∨ p3) → False) ∧ ((p0 → p2) ∧ (p2 → p0)))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_5
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p1 p7 : Prop)
theorem file15_36247 : ((((((False → p7) ∨ (p1 ∨ p5)) → False) → False) → False) → False) := by
  intro assump_25
  have assump_42 : ((((False → p7) ∨ (p1 ∨ p5)) → False) → False) := by
    intro assump_29
    have assump_43 : ((False → p7) ∨ (p1 ∨ p5)) := by
      apply Or.inl
      intro assump_33
      apply False.elim assump_33
    let assump_32 := assump_29 assump_43
    apply False.elim assump_32
  let assump_28 := assump_25 assump_42
  apply False.elim assump_28


variable (p7 p4 p0 p1 : Prop)
theorem file15_36752 : (((((p1 → p1) → (p4 ∨ True)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p1 → p1) → (p4 ∨ True)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p1 p4 p6 : Prop)
theorem file15_37127 : (((((p6 ∨ p4) → False) ∧ ((p7 ∧ p6) ∧ (p1 → p6))) ∧ (((p1 → False) → (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_28 : ((p1 → False) → (False → False)) := by
            intro assump_21
            intro assump_22
            apply False.elim assump_22
          let assump_20 := assump_3 assump_28
          apply False.elim assump_20


variable (p3 p2 p1 p7 p4 p6 p0 : Prop)
theorem file15_37792 : (((((p1 ∨ False) → (p2 → p2)) → False) → (((p7 ∨ p3) ∨ (p0 → p0)) → False)) ∨ ((((p0 → False) ∧ (p4 ∨ p0)) ∧ ((p6 → False) ∨ (p3 → False))) ∨ (((p7 → False) → False) → ((p4 ∧ p1) → (p6 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      have assump_61 : ((p1 ∨ False) → (p2 → p2)) := by
        intro assump_12
        intro assump_13
        cases assump_12
        case inl assump_16 =>
          exact assump_13
        case inr assump_17 =>
          apply False.elim assump_17
      let assump_11 := assump_1 assump_61
      apply False.elim assump_11
    case inr assump_6 =>
      have assump_62 : ((p1 ∨ False) → (p2 → p2)) := by
        intro assump_30
        intro assump_31
        cases assump_30
        case inl assump_34 =>
          exact assump_31
        case inr assump_35 =>
          apply False.elim assump_35
      let assump_29 := assump_1 assump_62
      apply False.elim assump_29
  case inr assump_4 =>
    have assump_63 : ((p1 ∨ False) → (p2 → p2)) := by
      intro assump_48
      intro assump_49
      cases assump_48
      case inl assump_52 =>
        exact assump_49
      case inr assump_53 =>
        apply False.elim assump_53
    let assump_47 := assump_1 assump_63
    apply False.elim assump_47


variable (p3 p6 p5 p7 p4 p2 p1 : Prop)
theorem file15_39198 : (((((p3 → p4) → False) ∨ ((p4 → p7) ∧ (p6 ∨ p5))) ∧ (((p1 → p6) ∧ (p5 ∧ p7)) → ((p7 → False) → (p3 ∧ p6)))) → ((((p2 → p1) ∧ (p1 → False)) → ((True ∧ p7) ∨ (p7 → False))) → (((False ∧ p2) → (p4 ∨ p2)) ∨ ((p7 ∧ p2) → (p7 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    case inr assump_8 =>
      cases assump_8
      case intro assump_18 assump_19 =>
        cases assump_19
        case inl assump_22 =>
          apply Or.inl
          intro assump_28
          cases assump_28
          case intro assump_29 assump_30 =>
            apply False.elim assump_29
        case inr assump_23 =>
          apply Or.inl
          intro assump_37
          cases assump_37
          case intro assump_38 assump_39 =>
            apply False.elim assump_38


variable (p3 p5 p1 p0 p7 p6 p2 : Prop)
theorem file15_40253 : (((((p1 ∨ True) ∧ (p5 ∧ p2)) ∨ ((p2 → True) → False)) → (((p3 ∨ p7) → (p6 → p5)) → ((p5 ∧ p0) → (p2 ∨ p7)))) ∨ ((((p3 → p2) ∨ (p1 ∨ p7)) → ((p3 ∧ p6) ∧ (p2 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case intro assump_20 assump_21 =>
            apply Or.inl
            exact assump_21
        case inr assump_17 =>
          cases assump_15
          case intro assump_28 assump_29 =>
            apply Or.inl
            exact assump_29
    case inr assump_13 =>
      have assump_41 : (p2 → True) := by
        intro assump_37
        apply True.intro
      let assump_36 := assump_13 assump_41
      apply False.elim assump_36


variable (p6 p0 p2 p4 p1 p3 p5 p7 : Prop)
theorem file15_41247 : (((((p1 ∧ p4) ∧ (p7 ∧ p4)) → False) → (((True ∧ p6) ∨ (p4 ∨ p4)) ∨ ((p0 ∧ p1) → (False → False)))) ∨ ((((p1 ∨ p5) ∨ (p4 → False)) → ((p3 → False) ∧ (True ∨ p6))) ∧ (((True ∧ p1) ∨ (p5 ∨ p3)) ∧ ((p0 → p2) → (p6 ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p7 p0 p4 p6 : Prop)
theorem file15_41636 : (((((p7 ∧ p0) ∨ (p4 → p4)) ∨ ((p6 → False) → (True ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p7 ∧ p0) ∨ (p4 → p4)) ∨ ((p6 → False) → (True ∨ p4))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p1 p3 p6 p0 : Prop)
theorem file15_42012 : ((((((p3 ∧ p3) → (p3 ∨ p1)) → False) → (((p0 ∧ p4) ∨ (p6 → False)) → ((True → False) → False))) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p3 ∧ p3) → (p3 ∨ p1)) → False) → (((p0 ∧ p4) ∨ (p6 → False)) → ((True → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_50 : ((p3 ∧ p3) → (p3 ∨ p1)) := by
          intro assump_21
          cases assump_21
          case intro assump_22 assump_23 =>
            apply Or.inl
            exact assump_23
        let assump_20 := assump_5 assump_50
        apply False.elim assump_20
    case inr assump_11 =>
      have assump_51 : ((p3 ∧ p3) → (p3 ∨ p1)) := by
        intro assump_36
        cases assump_36
        case intro assump_37 assump_38 =>
          apply Or.inl
          exact assump_38
      let assump_35 := assump_5 assump_51
      apply False.elim assump_35
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p3 p5 p7 p1 p6 p4 p0 p2 : Prop)
theorem file15_43139 : ((((((p3 ∨ p6) ∨ (p7 → True)) ∨ ((False ∨ p1) → False)) ∧ (((True ∧ p7) → False) → ((p0 → p2) ∧ (p5 → False)))) ∧ ((((p7 ∧ p6) ∨ (p6 → p6)) → False) ∧ (((p4 ∧ p4) ∨ (p5 ∨ p1)) ∧ ((p5 → p5) → (p3 → False))))) → False) := by
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
          case inl assump_10 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    have assump_276 : (p5 → p5) := by
                      intro assump_33
                      exact assump_33
                    let assump_32 := assump_21 assump_276
                    have assump_277 : p3 := by
                      exact assump_10
                    let assump_36 := assump_32 assump_277
                    apply False.elim assump_36
                case inr assump_23 =>
                  cases assump_23
                  case inl assump_40 =>
                    have assump_278 : (p5 → p5) := by
                      intro assump_47
                      exact assump_47
                    let assump_46 := assump_21 assump_278
                    have assump_279 : p3 := by
                      exact assump_10
                    let assump_50 := assump_46 assump_279
                    apply False.elim assump_50
                  case inr assump_41 =>
                    have assump_280 : (p5 → p5) := by
                      intro assump_59
                      exact assump_59
                    let assump_58 := assump_21 assump_280
                    have assump_281 : p3 := by
                      exact assump_10
                    let assump_62 := assump_58 assump_281
                    apply False.elim assump_62
          case inr assump_11 =>
            cases assump_3
            case intro assump_70 assump_71 =>
              cases assump_71
              case intro assump_74 assump_75 =>
                cases assump_74
                case inl assump_76 =>
                  cases assump_76
                  case intro assump_78 assump_79 =>
                    have assump_282 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                      apply Or.inr
                      intro assump_94
                      exact assump_94
                    let assump_93 := assump_70 assump_282
                    apply False.elim assump_93
                case inr assump_77 =>
                  cases assump_77
                  case inl assump_100 =>
                    have assump_283 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                      apply Or.inr
                      intro assump_113
                      exact assump_113
                    let assump_112 := assump_70 assump_283
                    apply False.elim assump_112
                  case inr assump_101 =>
                    have assump_284 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                      apply Or.inr
                      intro assump_130
                      exact assump_130
                    let assump_129 := assump_70 assump_284
                    apply False.elim assump_129
        case inr assump_9 =>
          cases assump_3
          case intro assump_140 assump_141 =>
            cases assump_141
            case intro assump_144 assump_145 =>
              cases assump_144
              case inl assump_146 =>
                cases assump_146
                case intro assump_148 assump_149 =>
                  have assump_285 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                    apply Or.inr
                    intro assump_164
                    exact assump_164
                  let assump_163 := assump_140 assump_285
                  apply False.elim assump_163
              case inr assump_147 =>
                cases assump_147
                case inl assump_170 =>
                  have assump_286 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                    apply Or.inr
                    intro assump_183
                    exact assump_183
                  let assump_182 := assump_140 assump_286
                  apply False.elim assump_182
                case inr assump_171 =>
                  have assump_287 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                    apply Or.inr
                    intro assump_200
                    exact assump_200
                  let assump_199 := assump_140 assump_287
                  apply False.elim assump_199
      case inr assump_7 =>
        cases assump_3
        case intro assump_210 assump_211 =>
          cases assump_211
          case intro assump_214 assump_215 =>
            cases assump_214
            case inl assump_216 =>
              cases assump_216
              case intro assump_218 assump_219 =>
                have assump_288 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                  apply Or.inr
                  intro assump_234
                  exact assump_234
                let assump_233 := assump_210 assump_288
                apply False.elim assump_233
            case inr assump_217 =>
              cases assump_217
              case inl assump_240 =>
                have assump_289 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                  apply Or.inr
                  intro assump_253
                  exact assump_253
                let assump_252 := assump_210 assump_289
                apply False.elim assump_252
              case inr assump_241 =>
                have assump_290 : ((p7 ∧ p6) ∨ (p6 → p6)) := by
                  apply Or.inr
                  intro assump_270
                  exact assump_270
                let assump_269 := assump_210 assump_290
                apply False.elim assump_269


variable (p1 p2 p5 p3 p4 p0 p6 : Prop)
theorem file15_49207 : (((((p0 ∨ p1) ∧ (False ∧ p4)) → False) ∧ (((p3 → p3) → False) → ((p6 → False) ∧ (p1 → False)))) ∨ ((((True → p6) ∧ (False → False)) ∧ ((p3 → False) ∨ (False → p5))) → (((p2 → False) ∨ (p4 → True)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_54
  cases assump_54
  case intro assump_55 assump_56 =>
    cases assump_55
    case inl assump_57 =>
      cases assump_56
      case intro assump_61 assump_62 =>
        apply False.elim assump_61
    case inr assump_58 =>
      cases assump_56
      case intro assump_67 assump_68 =>
        apply False.elim assump_67
  intro assump_71
  apply And.intro
  intro assump_72
  have assump_96 : (p3 → p3) := by
    intro assump_78
    exact assump_78
  let assump_77 := assump_71 assump_96
  apply False.elim assump_77
  intro assump_84
  have assump_97 : (p3 → p3) := by
    intro assump_90
    exact assump_90
  let assump_89 := assump_71 assump_97
  apply False.elim assump_89


variable (p6 p1 p2 p7 p0 p4 p3 : Prop)
theorem file15_50213 : (((((p7 ∨ p6) ∨ (p6 → True)) ∧ ((p3 → False) ∧ (p0 ∧ p6))) ∧ (((True ∨ p3) → False) ∧ ((p3 ∨ True) → False))) → ((((p2 → False) → (p7 ∧ p0)) ∨ ((p1 → False) → False)) ∧ (((True → p0) → (p2 ∧ p2)) → ((p2 → False) → (p4 ∧ True))))) := by
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
          cases assump_5
          case intro assump_12 assump_13 =>
            cases assump_13
            case intro assump_16 assump_17 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                apply Or.inl
                intro assump_28
                apply And.intro
                exact assump_8
                exact assump_16
        case inr assump_9 =>
          cases assump_5
          case intro assump_35 assump_36 =>
            cases assump_36
            case intro assump_39 assump_40 =>
              cases assump_3
              case intro assump_45 assump_46 =>
                apply Or.inl
                intro assump_51
                apply And.intro
                have assump_169 : (p3 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_55 := assump_46 assump_169
                apply False.elim assump_55
                exact assump_39
      case inr assump_7 =>
        cases assump_5
        case intro assump_63 assump_64 =>
          cases assump_64
          case intro assump_67 assump_68 =>
            cases assump_3
            case intro assump_73 assump_74 =>
              apply Or.inl
              intro assump_79
              apply And.intro
              have assump_170 : (p3 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_83 := assump_74 assump_170
              apply False.elim assump_83
              exact assump_67
  intro assump_89
  intro assump_90
  apply And.intro
  cases assump_1
  case intro assump_95 assump_96 =>
    cases assump_95
    case intro assump_97 assump_98 =>
      cases assump_97
      case inl assump_99 =>
        cases assump_99
        case inl assump_101 =>
          cases assump_98
          case intro assump_105 assump_106 =>
            cases assump_106
            case intro assump_109 assump_110 =>
              cases assump_96
              case intro assump_115 assump_116 =>
                have assump_171 : (p3 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_121 := assump_116 assump_171
                apply False.elim assump_121
        case inr assump_102 =>
          cases assump_98
          case intro assump_127 assump_128 =>
            cases assump_128
            case intro assump_131 assump_132 =>
              cases assump_96
              case intro assump_137 assump_138 =>
                have assump_172 : (p3 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_143 := assump_138 assump_172
                apply False.elim assump_143
      case inr assump_100 =>
        cases assump_98
        case intro assump_149 assump_150 =>
          cases assump_150
          case intro assump_153 assump_154 =>
            cases assump_96
            case intro assump_159 assump_160 =>
              have assump_173 : (p3 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_165 := assump_160 assump_173
              apply False.elim assump_165
  apply True.intro


variable (p7 p1 p5 p2 p0 p4 : Prop)
theorem file15_53940 : ((((((False ∧ p7) ∧ (p2 ∨ True)) → False) ∨ (((p7 → p5) ∨ (p1 ∧ p1)) ∨ ((False ∨ p4) → (p0 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ p7) ∧ (p2 ∨ True)) → False) ∨ (((p7 → p5) ∨ (p1 ∧ p1)) ∨ ((False ∨ p4) → (p0 ∧ p4)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p0 p6 p3 p2 p5 p4 : Prop)
theorem file15_54516 : (((((p1 → p1) → (False → False)) ∨ ((p5 → p2) ∧ (p4 → p0))) → False) → ((((p0 ∨ p2) → (p6 ∨ False)) → ((p2 → p3) ∧ (p2 → True))) → False)) := by
  intro assump_5
  intro assump_6
  have assump_19 : (((p1 → p1) → (False → False)) ∨ ((p5 → p2) ∧ (p4 → p0))) := by
    apply Or.inl
    intro assump_12
    intro assump_13
    apply False.elim assump_13
  let assump_11 := assump_5 assump_19
  apply False.elim assump_11


variable (p1 p6 p7 p3 p5 p2 p0 p4 : Prop)
theorem file15_54999 : (((((p1 ∧ p7) ∧ (p3 ∧ p7)) ∧ ((p2 ∧ p4) ∧ (p0 → False))) ∧ (((p3 ∧ p6) ∧ (p4 → False)) ∨ ((p0 ∨ p7) ∧ (p5 ∨ p4)))) → ((((p5 → p0) → (p6 ∨ p4)) ∨ ((False ∧ p2) → False)) ∨ (((True ∨ p0) ∧ (p1 ∧ p4)) ∧ ((p1 → False) ∧ (p4 ∨ True))))) := by
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
            cases assump_5
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_3
                case inl assump_30 =>
                  cases assump_30
                  case intro assump_32 assump_33 =>
                    cases assump_32
                    case intro assump_34 assump_35 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_42
                      apply Or.inl
                      exact assump_35
                case inr assump_31 =>
                  cases assump_31
                  case intro assump_45 assump_46 =>
                    cases assump_45
                    case inl assump_47 =>
                      cases assump_46
                      case inl assump_51 =>
                        apply Or.inl
                        apply Or.inl
                        intro assump_55
                        apply Or.inr
                        exact assump_23
                      case inr assump_52 =>
                        apply Or.inl
                        apply Or.inl
                        intro assump_60
                        apply Or.inr
                        exact assump_52
                    case inr assump_48 =>
                      cases assump_46
                      case inl assump_65 =>
                        apply Or.inl
                        apply Or.inl
                        intro assump_69
                        apply Or.inr
                        exact assump_23
                      case inr assump_66 =>
                        apply Or.inl
                        apply Or.inl
                        intro assump_74
                        apply Or.inr
                        exact assump_66


variable (p3 p4 p0 p5 p6 p2 p7 p1 : Prop)
theorem file15_57454 : (((((p4 ∧ p0) ∨ (p3 ∨ p7)) ∨ ((p4 ∨ p0) ∨ (False → False))) ∨ (((p6 → p5) → (p0 ∧ p0)) ∧ ((False → p7) ∨ (p3 ∨ p2)))) ∨ ((((p1 ∧ p2) → (p2 → False)) ∨ ((p7 → p2) ∨ (p6 ∨ p5))) → (((p0 → p3) → False) ∨ ((p3 ∨ p5) ∧ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  intro assump_1
  apply False.elim assump_1


variable (p4 p2 p0 p7 p3 p6 : Prop)
theorem file15_57856 : ((((((p2 ∧ False) → (False → False)) → False) ∧ (((p6 ∨ p6) ∨ (False → p4)) ∧ ((p4 ∧ p3) ∨ (p4 → False)))) ∨ ((((True ∨ p7) ∨ (True → p0)) → ((p6 ∨ p2) ∨ (p2 ∨ True))) ∧ (((p4 ∨ True) ∨ (p0 → p3)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_13
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                have assump_127 : ((p2 ∧ False) → (False → False)) := by
                  intro assump_32
                  intro assump_33
                  apply False.elim assump_33
                let assump_31 := assump_8 assump_127
                apply False.elim assump_31
            case inr assump_21 =>
              have assump_128 : ((p2 ∧ False) → (False → False)) := by
                intro assump_44
                intro assump_45
                apply False.elim assump_45
              let assump_43 := assump_8 assump_128
              apply False.elim assump_43
          case inr assump_17 =>
            cases assump_13
            case inl assump_53 =>
              cases assump_53
              case intro assump_55 assump_56 =>
                have assump_129 : ((p2 ∧ False) → (False → False)) := by
                  intro assump_65
                  intro assump_66
                  apply False.elim assump_66
                let assump_64 := assump_8 assump_129
                apply False.elim assump_64
            case inr assump_54 =>
              have assump_130 : ((p2 ∧ False) → (False → False)) := by
                intro assump_77
                intro assump_78
                apply False.elim assump_78
              let assump_76 := assump_8 assump_130
              apply False.elim assump_76
        case inr assump_15 =>
          cases assump_13
          case inl assump_86 =>
            cases assump_86
            case intro assump_88 assump_89 =>
              have assump_131 : ((p2 ∧ False) → (False → False)) := by
                intro assump_98
                intro assump_99
                apply False.elim assump_99
              let assump_97 := assump_8 assump_131
              apply False.elim assump_97
          case inr assump_87 =>
            have assump_132 : ((p2 ∧ False) → (False → False)) := by
              intro assump_110
              intro assump_111
              apply False.elim assump_111
            let assump_109 := assump_8 assump_132
            apply False.elim assump_109
  case inr assump_7 =>
    cases assump_7
    case intro assump_117 assump_118 =>
      have assump_133 : ((p4 ∨ True) ∨ (p0 → p3)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_123 := assump_118 assump_133
      apply False.elim assump_123


variable (p7 p2 p1 p5 p0 p3 p6 : Prop)
theorem file15_60923 : (((((p1 ∧ p5) ∨ (p2 ∨ p1)) ∨ ((p2 → False) ∨ (False → False))) → False) → ((((False ∨ p7) ∧ (False → p1)) → ((p2 ∨ p0) ∨ (False → False))) ∨ (((p7 → False) ∧ (p3 → p2)) → ((False ∨ p5) ∨ (p6 ∨ p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      apply False.elim assump_7
    case inr assump_8 =>
      apply Or.inr
      intro assump_15
      apply False.elim assump_15


variable (p6 p5 p1 : Prop)
theorem file15_61456 : (((((p1 → False) → False) → ((p6 ∧ p1) ∨ (p5 → p5))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p1 → False) → False) → ((p6 ∧ p1) ∨ (p5 → p5))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p3 p6 p7 p2 p5 : Prop)
theorem file15_61825 : (((((True ∧ p2) ∧ (p3 → False)) → False) ∧ (((True ∨ p7) → False) ∨ ((True → False) ∨ (False ∨ p1)))) → ((((True → False) ∧ (p2 → False)) ∨ ((p3 ∧ p5) → (p2 → False))) → (((p2 ∨ False) ∨ (True ∨ p2)) ∨ ((p3 ∧ p5) → (p3 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply True.intro
        case inr assump_16 =>
          cases assump_16
          case inl assump_19 =>
            apply Or.inl
            apply Or.inr
            apply Or.inl
            apply True.intro
          case inr assump_20 =>
            cases assump_20
            case inl assump_23 =>
              apply False.elim assump_23
            case inr assump_24 =>
              apply Or.inl
              apply Or.inr
              apply Or.inl
              apply True.intro
  case inr assump_4 =>
    cases assump_1
    case intro assump_31 assump_32 =>
      cases assump_32
      case inl assump_35 =>
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
      case inr assump_36 =>
        cases assump_36
        case inl assump_39 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply True.intro
        case inr assump_40 =>
          cases assump_40
          case inl assump_43 =>
            apply False.elim assump_43
          case inr assump_44 =>
            apply Or.inl
            apply Or.inr
            apply Or.inl
            apply True.intro


variable (p0 p3 p2 p4 p1 p7 p6 : Prop)
theorem file15_63595 : (((((False ∧ p4) → False) → ((False ∧ p6) → False)) ∨ (((p6 ∨ p7) → False) ∨ ((p6 → p0) → (p0 → False)))) ∧ ((((p0 → False) → (p4 ∧ p4)) → ((p4 → p4) ∨ (p4 ∨ p7))) ∨ (((True → p0) → (p2 ∧ p6)) → ((p1 ∧ p3) ∧ (p0 ∨ p1))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3
  apply Or.inl
  intro assump_7
  apply Or.inl
  intro assump_10
  exact assump_10


variable (p6 p4 p3 p0 p7 p2 p1 p5 : Prop)
theorem file15_64120 : ((((((p6 → False) ∧ (p0 → p6)) ∧ ((p2 ∨ p2) → (p1 → False))) ∧ (((True ∨ p1) → False) → ((p7 ∧ True) ∧ (p5 → False)))) ∧ ((((p2 ∨ p2) → (p3 ∧ p5)) → ((p1 ∨ p5) → (p0 → False))) ∧ (((p4 → False) → (p4 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            have assump_30 : ((p4 → False) → (p4 → True)) := by
              intro assump_25
              intro assump_26
              apply True.intro
            let assump_24 := assump_19 assump_30
            apply False.elim assump_24


variable (p2 p3 p5 p4 : Prop)
theorem file15_64966 : (((((p4 → p3) → False) ∨ ((p4 ∧ p2) ∨ (p2 → False))) ∧ (((False ∧ p3) ∨ (p5 → True)) → False)) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case inl assump_22 =>
      have assump_57 : ((False ∧ p3) ∨ (p5 → True)) := by
        apply Or.inr
        intro assump_29
        apply True.intro
      let assump_28 := assump_21 assump_57
      apply False.elim assump_28
    case inr assump_23 =>
      cases assump_23
      case inl assump_33 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          have assump_58 : ((False ∧ p3) ∨ (p5 → True)) := by
            apply Or.inr
            intro assump_44
            apply True.intro
          let assump_43 := assump_21 assump_58
          apply False.elim assump_43
      case inr assump_34 =>
        have assump_59 : ((False ∧ p3) ∨ (p5 → True)) := by
          apply Or.inr
          intro assump_53
          apply True.intro
        let assump_52 := assump_21 assump_59
        apply False.elim assump_52


variable (p5 p4 p3 p0 p7 p2 p1 p6 : Prop)
theorem file15_66078 : (((((p2 → p6) ∧ (p6 ∨ p6)) ∧ ((p6 ∨ True) → False)) → (((p5 ∧ p5) → (p3 → p3)) → False)) ∨ ((((p4 ∨ p0) → (p7 ∧ False)) ∧ ((False → False) ∧ (True ∨ p4))) → (((True ∨ p1) ∧ (False ∧ p6)) → ((False → False) → (p2 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        have assump_29 : (p6 ∨ True) := by
          apply Or.inl
          exact assump_11
        let assump_17 := assump_6 assump_29
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_30 : (p6 ∨ True) := by
          apply Or.inl
          exact assump_12
        let assump_25 := assump_6 assump_30
        apply False.elim assump_25


variable (p4 p7 : Prop)
theorem file15_66928 : ((((((p4 ∧ False) → (p7 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p4 ∧ False) → (p7 → False)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p4 ∧ False) → (p7 → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p5 p4 p3 p7 : Prop)
theorem file15_67502 : ((((((False ∧ p4) → False) ∧ ((False → False) ∨ (p0 ∧ p7))) ∨ (((p3 → p5) → (p5 ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∧ p4) → False) ∧ ((False → False) ∨ (p0 ∧ p7))) ∨ (((p3 → p5) → (p5 ∨ False)) → False)) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    apply Or.inl
    intro assump_10
    apply False.elim assump_10
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 : Prop)
theorem file15_68087 : ((((((False ∧ p6) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p6) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ p6) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p0 p4 p6 p3 : Prop)
theorem file15_68615 : ((((((p3 ∧ p0) → (p6 ∨ p3)) → False) → (((p0 ∨ True) ∨ (True ∧ p0)) ∧ ((p3 ∧ p4) → False))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p3 ∧ p0) → (p6 ∨ p3)) → False) → (((p0 ∨ True) ∨ (True ∧ p0)) ∧ ((p3 ∧ p4) → False))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    apply Or.inr
    apply True.intro
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_32 : ((p3 ∧ p0) → (p6 ∨ p3)) := by
        intro assump_18
        cases assump_18
        case intro assump_19 assump_20 =>
          apply Or.inr
          exact assump_19
      let assump_17 := assump_5 assump_32
      apply False.elim assump_17
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p3 p6 p7 p5 p0 p4 : Prop)
theorem file15_69427 : ((((((p1 ∧ False) ∧ (p5 ∧ p0)) → ((False ∧ p6) → False)) ∨ (((p3 → False) ∧ (p4 ∨ p1)) → ((p7 → True) → (p1 → False)))) → False) → False) := by
  intro assump_16
  have assump_29 : ((((p1 ∧ False) ∧ (p5 ∧ p0)) → ((False ∧ p6) → False)) ∨ (((p3 → False) ∧ (p4 ∨ p1)) → ((p7 → True) → (p1 → False)))) := by
    apply Or.inl
    intro assump_20
    intro assump_21
    cases assump_21
    case intro assump_22 assump_23 =>
      apply False.elim assump_22
  let assump_19 := assump_16 assump_29
  apply False.elim assump_19


variable (p1 p6 p2 p3 p4 p0 : Prop)
theorem file15_70008 : ((((((p1 → False) ∧ (p3 ∨ False)) → ((p1 → p0) ∨ (False ∧ p2))) ∧ (((True → False) → False) ∨ ((p4 ∧ p0) → (p6 → False)))) → False) → False) := by
  intro assump_34
  have assump_68 : ((((p1 → False) ∧ (p3 ∨ False)) → ((p1 → p0) ∨ (False ∧ p2))) ∧ (((True → False) → False) ∨ ((p4 ∧ p0) → (p6 → False)))) := by
    apply And.intro
    intro assump_38
    cases assump_38
    case intro assump_39 assump_40 =>
      cases assump_40
      case inl assump_43 =>
        apply Or.inl
        intro assump_47
        have assump_69 : p1 := by
          exact assump_47
        let assump_52 := assump_39 assump_69
        apply False.elim assump_52
      case inr assump_44 =>
        apply False.elim assump_44
    apply Or.inl
    intro assump_58
    have assump_70 : True := by
      apply True.intro
    let assump_61 := assump_58 assump_70
    apply False.elim assump_61
  let assump_37 := assump_34 assump_68
  apply False.elim assump_37


variable (p0 p1 p7 : Prop)
theorem file15_70998 : ((((((p7 → True) ∧ (True ∨ p1)) → False) → (((p0 → False) ∧ (p1 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p7 → True) ∧ (True ∨ p1)) → False) → (((p0 → False) ∧ (p1 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_24 : ((p7 → True) ∧ (True ∨ p1)) := by
        apply And.intro
        intro assump_16
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_15 := assump_5 assump_24
      apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p6 p4 p5 p0 p7 p2 p3 : Prop)
theorem file15_71702 : ((((((True → p6) → (p6 → p7)) ∨ ((p0 ∨ p7) → (p0 → False))) → False) ∧ ((((p5 → False) → (p2 ∨ p2)) ∨ ((p6 → False) ∨ (p7 ∨ p5))) ∧ (((p4 → True) → False) ∧ ((True ∧ p3) ∧ (p6 → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_106 : (p4 → True) := by
                intro assump_29
                apply True.intro
              let assump_28 := assump_12 assump_106
              apply False.elim assump_28
      case inr assump_9 =>
        cases assump_9
        case inl assump_33 =>
          cases assump_7
          case intro assump_37 assump_38 =>
            cases assump_38
            case intro assump_41 assump_42 =>
              cases assump_41
              case intro assump_43 assump_44 =>
                have assump_107 : (p4 → True) := by
                  intro assump_54
                  apply True.intro
                let assump_53 := assump_37 assump_107
                apply False.elim assump_53
        case inr assump_34 =>
          cases assump_34
          case inl assump_58 =>
            cases assump_7
            case intro assump_62 assump_63 =>
              cases assump_63
              case intro assump_66 assump_67 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  have assump_108 : (p4 → True) := by
                    intro assump_79
                    apply True.intro
                  let assump_78 := assump_62 assump_108
                  apply False.elim assump_78
          case inr assump_59 =>
            cases assump_7
            case intro assump_85 assump_86 =>
              cases assump_86
              case intro assump_89 assump_90 =>
                cases assump_89
                case intro assump_91 assump_92 =>
                  have assump_109 : (p4 → True) := by
                    intro assump_102
                    apply True.intro
                  let assump_101 := assump_85 assump_109
                  apply False.elim assump_101


variable (p5 p0 p3 p2 p4 : Prop)
theorem file15_74112 : ((((((False → False) → (False ∧ p5)) → ((p0 ∧ p4) → False)) → False) ∧ ((((True ∧ False) ∧ (p5 → p3)) ∧ ((p2 → True) ∧ (p2 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : (((False → False) → (False ∧ p5)) → ((p0 ∧ p4) → False)) := by
      intro assump_10
      intro assump_11
      cases assump_11
      case intro assump_12 assump_13 =>
        have assump_32 : (False → False) := by
          intro assump_21
          apply False.elim assump_21
        let assump_20 := assump_10 assump_32
        let assump_24 := And.left assump_20
        apply False.elim assump_24
    let assump_9 := assump_2 assump_31
    apply False.elim assump_9


variable (p3 p1 p7 p2 p6 p0 : Prop)
theorem file15_74892 : ((((((True ∨ False) ∧ (True ∨ p3)) → False) → (((p7 ∨ True) ∧ (p7 ∨ p1)) → False)) ∧ ((((False → False) ∨ (p2 → p0)) ∨ ((p6 → p7) → (p2 ∧ True))) → False)) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    have assump_24 : (((False → False) ∨ (p2 → p0)) ∨ ((p6 → p7) → (p2 ∧ True))) := by
      apply Or.inl
      apply Or.inl
      intro assump_18
      apply False.elim assump_18
    let assump_17 := assump_12 assump_24
    apply False.elim assump_17


variable (p0 p3 p1 p6 p7 p4 p5 : Prop)
theorem file15_75450 : ((((((p0 ∧ p1) ∨ (False ∧ p3)) ∨ ((True → False) → (True ∨ p4))) → False) ∧ ((((p3 → False) ∧ (p1 → p5)) ∧ ((p1 ∨ p7) → (p0 ∧ p4))) ∧ (((p0 → p6) ∨ (True ∨ p4)) ∨ ((True ∧ True) ∨ (p5 ∨ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case inl assump_18 =>
            cases assump_18
            case inl assump_20 =>
              have assump_108 : (((p0 ∧ p1) ∨ (False ∧ p3)) ∨ ((True → False) → (True ∨ p4))) := by
                apply Or.inr
                intro assump_29
                apply Or.inl
                apply True.intro
              let assump_28 := assump_2 assump_108
              apply False.elim assump_28
            case inr assump_21 =>
              cases assump_21
              case inl assump_35 =>
                have assump_109 : (((p0 ∧ p1) ∨ (False ∧ p3)) ∨ ((True → False) → (True ∨ p4))) := by
                  apply Or.inr
                  intro assump_43
                  apply Or.inl
                  apply True.intro
                let assump_42 := assump_2 assump_109
                apply False.elim assump_42
              case inr assump_36 =>
                have assump_110 : (((p0 ∧ p1) ∨ (False ∧ p3)) ∨ ((True → False) → (True ∨ p4))) := by
                  apply Or.inr
                  intro assump_56
                  apply Or.inl
                  apply True.intro
                let assump_55 := assump_2 assump_110
                apply False.elim assump_55
          case inr assump_19 =>
            cases assump_19
            case inl assump_62 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                have assump_111 : (((p0 ∧ p1) ∨ (False ∧ p3)) ∨ ((True → False) → (True ∨ p4))) := by
                  apply Or.inr
                  intro assump_74
                  apply Or.inl
                  apply True.intro
                let assump_73 := assump_2 assump_111
                apply False.elim assump_73
            case inr assump_63 =>
              cases assump_63
              case inl assump_80 =>
                have assump_112 : (((p0 ∧ p1) ∨ (False ∧ p3)) ∨ ((True → False) → (True ∨ p4))) := by
                  apply Or.inr
                  intro assump_89
                  apply Or.inl
                  apply True.intro
                let assump_88 := assump_2 assump_112
                apply False.elim assump_88
              case inr assump_81 =>
                have assump_113 : (((p0 ∧ p1) ∨ (False ∧ p3)) ∨ ((True → False) → (True ∨ p4))) := by
                  apply Or.inr
                  intro assump_102
                  apply Or.inl
                  apply True.intro
                let assump_101 := assump_2 assump_113
                apply False.elim assump_101


variable (p5 p6 p2 p3 p4 p7 p1 : Prop)
theorem file15_78495 : ((((((p6 ∧ False) → (p1 ∨ p4)) ∧ ((p6 ∧ p3) ∧ (True ∧ False))) ∧ (((p5 → p7) → (p2 ∧ p2)) → False)) ∧ ((((False → False) → (p5 → p1)) ∨ ((p4 ∧ p6) → False)) ∨ (((p7 ∧ p1) ∧ (False → False)) → False))) → False) := by
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
            cases assump_11
            case intro assump_18 assump_19 =>
              apply False.elim assump_19


variable (p7 p1 p2 p6 p0 : Prop)
theorem file15_79200 : ((((((p6 → True) ∧ (True → False)) ∧ ((p0 ∧ p1) → False)) → (((p1 ∧ p7) → False) → ((p2 → p0) → (p6 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p6 → True) ∧ (True → False)) ∧ ((p0 ∧ p1) → False)) → (((p1 ∧ p7) → False) → ((p2 → p0) → (p6 → True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p0 p7 p4 p5 p2 p6 : Prop)
theorem file15_79711 : ((((((p2 → False) → (p0 ∧ p1)) ∨ ((p4 ∧ p5) → False)) → (((p7 ∧ p6) ∨ (p2 → p0)) → False)) ∧ ((((p1 → True) ∨ (p4 → False)) → ((p4 ∨ True) → False)) ∧ (((p7 ∨ p6) → False) ∨ ((p2 ∨ p5) → (False → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_30 : ((p1 → True) ∨ (p4 → False)) := by
          apply Or.inl
          intro assump_16
          apply True.intro
        let assump_15 := assump_6 assump_30
        have assump_31 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_17 := assump_15 assump_31
        apply False.elim assump_17
      case inr assump_11 =>
        have assump_32 : ((p1 → True) ∨ (p4 → False)) := by
          apply Or.inl
          intro assump_25
          apply True.intro
        let assump_24 := assump_6 assump_32
        have assump_33 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_26 := assump_24 assump_33
        apply False.elim assump_26


variable (p4 p7 p6 p5 p3 p0 : Prop)
theorem file15_80896 : (((((p3 ∨ p5) ∨ (False → p6)) → False) → False) ∨ ((((p4 → p6) ∧ (p0 → p6)) ∨ ((p5 → p7) → (p0 ∧ p6))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p3 ∨ p5) ∨ (False → p6)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p2 : Prop)
theorem file15_81278 : ((((((False ∧ p5) ∧ (p2 → p5)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∧ p5) ∧ (p2 → p5)) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p6 p1 p4 p0 p5 : Prop)
theorem file15_81840 : ((((((False → False) → False) ∨ ((p6 ∨ p7) ∨ (p5 ∧ True))) ∧ (((p1 → False) → False) ∧ ((p6 ∨ p5) ∧ (p5 ∧ p7)))) ∧ ((((p1 → p1) → False) ∧ ((p1 → False) ∧ (True → p4))) ∧ (((p7 ∨ p0) ∧ (p1 ∧ True)) → False))) → False) := by
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_19
      case inl assump_21 =>
        cases assump_20
        case intro assump_25 assump_26 =>
          cases assump_26
          case intro assump_29 assump_30 =>
            cases assump_29
            case inl assump_31 =>
              cases assump_30
              case intro assump_35 assump_36 =>
                cases assump_18
                case intro assump_41 assump_42 =>
                  cases assump_41
                  case intro assump_43 assump_44 =>
                    cases assump_44
                    case intro assump_47 assump_48 =>
                      have assump_335 : (p1 → p1) := by
                        intro assump_60
                        exact assump_60
                      let assump_59 := assump_43 assump_335
                      apply False.elim assump_59
            case inr assump_32 =>
              cases assump_30
              case intro assump_68 assump_69 =>
                cases assump_18
                case intro assump_74 assump_75 =>
                  cases assump_74
                  case intro assump_76 assump_77 =>
                    cases assump_77
                    case intro assump_80 assump_81 =>
                      have assump_336 : (p1 → p1) := by
                        intro assump_93
                        exact assump_93
                      let assump_92 := assump_76 assump_336
                      apply False.elim assump_92
      case inr assump_22 =>
        cases assump_22
        case inl assump_99 =>
          cases assump_99
          case inl assump_101 =>
            cases assump_20
            case intro assump_105 assump_106 =>
              cases assump_106
              case intro assump_109 assump_110 =>
                cases assump_109
                case inl assump_111 =>
                  cases assump_110
                  case intro assump_115 assump_116 =>
                    cases assump_18
                    case intro assump_121 assump_122 =>
                      cases assump_121
                      case intro assump_123 assump_124 =>
                        cases assump_124
                        case intro assump_127 assump_128 =>
                          have assump_337 : (p1 → p1) := by
                            intro assump_140
                            exact assump_140
                          let assump_139 := assump_123 assump_337
                          apply False.elim assump_139
                case inr assump_112 =>
                  cases assump_110
                  case intro assump_148 assump_149 =>
                    cases assump_18
                    case intro assump_154 assump_155 =>
                      cases assump_154
                      case intro assump_156 assump_157 =>
                        cases assump_157
                        case intro assump_160 assump_161 =>
                          have assump_338 : (p1 → p1) := by
                            intro assump_173
                            exact assump_173
                          let assump_172 := assump_156 assump_338
                          apply False.elim assump_172
          case inr assump_102 =>
            cases assump_20
            case intro assump_181 assump_182 =>
              cases assump_182
              case intro assump_185 assump_186 =>
                cases assump_185
                case inl assump_187 =>
                  cases assump_186
                  case intro assump_191 assump_192 =>
                    cases assump_18
                    case intro assump_197 assump_198 =>
                      cases assump_197
                      case intro assump_199 assump_200 =>
                        cases assump_200
                        case intro assump_203 assump_204 =>
                          have assump_339 : (p1 → p1) := by
                            intro assump_216
                            exact assump_216
                          let assump_215 := assump_199 assump_339
                          apply False.elim assump_215
                case inr assump_188 =>
                  cases assump_186
                  case intro assump_224 assump_225 =>
                    cases assump_18
                    case intro assump_230 assump_231 =>
                      cases assump_230
                      case intro assump_232 assump_233 =>
                        cases assump_233
                        case intro assump_236 assump_237 =>
                          have assump_340 : (p1 → p1) := by
                            intro assump_249
                            exact assump_249
                          let assump_248 := assump_232 assump_340
                          apply False.elim assump_248
        case inr assump_100 =>
          cases assump_100
          case intro assump_255 assump_256 =>
            cases assump_20
            case intro assump_261 assump_262 =>
              cases assump_262
              case intro assump_265 assump_266 =>
                cases assump_265
                case inl assump_267 =>
                  cases assump_266
                  case intro assump_271 assump_272 =>
                    cases assump_18
                    case intro assump_277 assump_278 =>
                      cases assump_277
                      case intro assump_279 assump_280 =>
                        cases assump_280
                        case intro assump_283 assump_284 =>
                          have assump_341 : (p1 → p1) := by
                            intro assump_296
                            exact assump_296
                          let assump_295 := assump_279 assump_341
                          apply False.elim assump_295
                case inr assump_268 =>
                  cases assump_266
                  case intro assump_304 assump_305 =>
                    cases assump_18
                    case intro assump_310 assump_311 =>
                      cases assump_310
                      case intro assump_312 assump_313 =>
                        cases assump_313
                        case intro assump_316 assump_317 =>
                          have assump_342 : (p1 → p1) := by
                            intro assump_329
                            exact assump_329
                          let assump_328 := assump_312 assump_342
                          apply False.elim assump_328


variable (p1 p5 p0 p7 : Prop)
theorem file15_88668 : ((((((p0 ∨ p0) ∨ (p7 → p1)) ∧ ((p5 → False) → (p0 → False))) → (((p1 → p1) ∨ (True → p5)) ∨ ((p1 → p0) ∨ (p5 → False)))) → False) → False) := by
  intro assump_5
  have assump_40 : ((((p0 ∨ p0) ∨ (p7 → p1)) ∧ ((p5 → False) → (p0 → False))) → (((p1 → p1) ∨ (True → p5)) ∨ ((p1 → p0) ∨ (p5 → False)))) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          apply Or.inl
          apply Or.inl
          intro assump_20
          exact assump_20
        case inr assump_15 =>
          apply Or.inl
          apply Or.inl
          intro assump_27
          exact assump_27
      case inr assump_13 =>
        apply Or.inl
        apply Or.inl
        intro assump_34
        exact assump_34
  let assump_8 := assump_5 assump_40
  apply False.elim assump_8


variable (p4 p1 : Prop)
theorem file15_89611 : (((((p4 ∧ p1) → (False → False)) ∨ ((p4 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : (((p4 ∧ p1) → (False → False)) ∨ ((p4 → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p7 p0 p1 p3 p2 : Prop)
theorem file15_90003 : ((((((p0 → False) ∨ (p7 ∨ p1)) ∨ ((p7 ∧ p4) → (p2 ∧ False))) → (((p1 → p3) → False) → False)) ∧ ((((p4 → True) → False) → ((p4 → False) ∨ (p0 → p3))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_30 : (((p4 → True) → False) → ((p4 → False) ∨ (p0 → p3))) := by
      intro assump_15
      apply Or.inl
      intro assump_18
      have assump_31 : (p4 → True) := by
        intro assump_23
        apply True.intro
      let assump_22 := assump_15 assump_31
      apply False.elim assump_22
    let assump_14 := assump_9 assump_30
    apply False.elim assump_14


variable (p0 p3 p1 : Prop)
theorem file15_90677 : (((((False ∧ p3) → False) ∧ ((p1 ∨ p3) → (p0 ∨ True))) → False) → False) := by
  intro assump_10
  have assump_29 : (((False ∧ p3) → False) ∧ ((p1 ∨ p3) → (p0 ∨ True))) := by
    apply And.intro
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_15
    intro assump_19
    cases assump_19
    case inl assump_20 =>
      apply Or.inr
      apply True.intro
    case inr assump_21 =>
      apply Or.inr
      apply True.intro
  let assump_13 := assump_10 assump_29
  apply False.elim assump_13


variable (p7 p1 p4 p6 p3 p0 : Prop)
theorem file15_91287 : (((((p7 → False) → (False → p0)) → ((p7 ∧ p0) ∧ (p3 ∧ p3))) → (((p3 ∨ True) ∧ (False ∧ p3)) → False)) ∨ ((((p7 ∨ p6) ∨ (p6 → False)) ∧ ((p1 ∨ p4) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_6 =>
      cases assump_4
      case intro assump_15 assump_16 =>
        apply False.elim assump_15


variable (p3 p5 p4 p1 p0 p2 : Prop)
theorem file15_91878 : (((((p5 → False) → (False → p1)) → ((p1 → p3) ∧ (p0 ∧ p3))) → False) → ((((p3 → False) → False) → False) → (((p2 ∧ True) ∧ (p4 → False)) ∨ ((p3 ∧ p0) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inr
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_30 : (((p5 → False) → (False → p1)) → ((p1 → p3) ∧ (p0 ∧ p3))) := by
      intro assump_17
      apply And.intro
      intro assump_18
      exact assump_8
      apply And.intro
      exact assump_9
      exact assump_8
    let assump_16 := assump_1 assump_30
    apply False.elim assump_16


variable (p4 p0 p5 p1 p2 p7 p3 : Prop)
theorem file15_92533 : (((((p1 → p3) ∧ (p4 ∧ p1)) ∧ ((False ∧ p4) ∧ (p1 ∧ p4))) → (((p0 ∨ p0) ∨ (True ∧ p0)) ∧ ((False → p5) ∧ (p2 → False)))) ∨ ((((p4 → False) → False) ∨ ((p5 → p5) → (True → p0))) ∨ (((True → False) ∨ (p2 → False)) ∨ ((p7 → p4) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
  apply And.intro
  intro assump_20
  apply False.elim assump_20
  intro assump_23
  cases assump_1
  case intro assump_26 assump_27 =>
    cases assump_26
    case intro assump_28 assump_29 =>
      cases assump_29
      case intro assump_32 assump_33 =>
        cases assump_27
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_40


variable (p5 p7 p3 p4 p2 p1 p6 p0 : Prop)
theorem file15_93668 : (((((p3 ∧ False) ∨ (p0 → False)) → ((p1 → p7) ∨ (True ∨ False))) → (((p0 ∨ p4) ∧ (p4 ∨ p7)) ∨ ((p1 ∨ True) ∨ (p5 ∨ p7)))) → ((((p6 → p0) ∧ (p2 → False)) ∧ ((p1 ∧ p6) → (p4 ∧ False))) → (((p5 ∨ p1) → (p6 → p6)) ∨ ((p0 ∧ p4) ∧ (p6 ∧ p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply Or.inl
      intro assump_15
      intro assump_16
      cases assump_15
      case inl assump_19 =>
        exact assump_16
      case inr assump_20 =>
        exact assump_16


variable (p6 p7 p1 p4 p2 p5 p0 : Prop)
theorem file15_94305 : ((((((p2 → p5) ∧ (p0 → p5)) ∧ ((p4 ∨ p7) → False)) ∨ (((False ∧ p7) → False) ∧ ((p4 ∧ p6) → False))) ∧ ((((False ∧ True) → (p1 ∧ p6)) → False) ∧ (((True → False) ∨ (p2 → True)) ∧ ((p7 ∧ p5) ∧ (p6 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_21
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    have assump_134 : True := by
                      apply True.intro
                    let assump_39 := assump_22 assump_134
                    apply False.elim assump_39
              case inr assump_23 =>
                cases assump_21
                case intro assump_45 assump_46 =>
                  cases assump_45
                  case intro assump_47 assump_48 =>
                    have assump_135 : ((False ∧ True) → (p1 ∧ p6)) := by
                      intro assump_60
                      apply And.intro
                      cases assump_60
                      case intro assump_61 assump_62 =>
                        apply False.elim assump_61
                      cases assump_60
                      case intro assump_65 assump_66 =>
                        apply False.elim assump_65
                    let assump_59 := assump_16 assump_135
                    apply False.elim assump_59
    case inr assump_5 =>
      cases assump_5
      case intro assump_72 assump_73 =>
        cases assump_3
        case intro assump_78 assump_79 =>
          cases assump_79
          case intro assump_82 assump_83 =>
            cases assump_82
            case inl assump_84 =>
              cases assump_83
              case intro assump_88 assump_89 =>
                cases assump_88
                case intro assump_90 assump_91 =>
                  have assump_136 : True := by
                    apply True.intro
                  let assump_101 := assump_84 assump_136
                  apply False.elim assump_101
            case inr assump_85 =>
              cases assump_83
              case intro assump_107 assump_108 =>
                cases assump_107
                case intro assump_109 assump_110 =>
                  have assump_137 : ((False ∧ True) → (p1 ∧ p6)) := by
                    intro assump_122
                    apply And.intro
                    cases assump_122
                    case intro assump_123 assump_124 =>
                      apply False.elim assump_123
                    cases assump_122
                    case intro assump_127 assump_128 =>
                      apply False.elim assump_127
                  let assump_121 := assump_78 assump_137
                  apply False.elim assump_121


variable (p1 p6 p4 p5 p0 : Prop)
theorem file15_97500 : ((((((p0 ∨ p1) → (p1 ∧ p0)) → ((p6 → True) ∨ (p1 → p0))) → False) ∨ ((((True ∧ False) → False) → ((p4 → True) ∨ (p5 → p5))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    have assump_30 : (((p0 ∨ p1) → (p1 ∧ p0)) → ((p6 → True) ∨ (p1 → p0))) := by
      intro assump_13
      apply Or.inl
      intro assump_16
      apply True.intro
    let assump_12 := assump_8 assump_30
    apply False.elim assump_12
  case inr assump_9 =>
    have assump_31 : (((True ∧ False) → False) → ((p4 → True) ∨ (p5 → p5))) := by
      intro assump_23
      apply Or.inl
      intro assump_26
      apply True.intro
    let assump_22 := assump_9 assump_31
    apply False.elim assump_22


variable (p0 p3 p1 p7 p6 p5 : Prop)
theorem file15_98266 : ((((((p0 → p7) → False) ∧ ((p5 ∧ False) ∧ (p1 ∧ False))) → (((p7 ∨ p3) ∧ (p0 → p6)) ∧ ((True → p1) ∨ (p5 → p3)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((p0 → p7) → False) ∧ ((p5 ∧ False) ∧ (p1 ∧ False))) → (((p7 ∨ p3) ∧ (p0 → p6)) ∧ ((True → p1) ∨ (p5 → p3)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    intro assump_18
    cases assump_5
    case intro assump_21 assump_22 =>
      cases assump_22
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          apply False.elim assump_28
    cases assump_5
    case intro assump_33 assump_34 =>
      cases assump_34
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          apply False.elim assump_40
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p1 p6 : Prop)
theorem file15_99413 : (((((True → False) ∧ (False → False)) → False) → False) → ((((p6 ∧ p1) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_23 : (((True → False) ∧ (False → False)) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_24 : True := by
        apply True.intro
      let assump_16 := assump_9 assump_24
      apply False.elim assump_16
  let assump_7 := assump_1 assump_23
  apply False.elim assump_7


variable (p3 p6 p0 p2 p5 p1 p4 : Prop)
theorem file15_99959 : (((((p2 → p4) → (False → False)) ∨ ((p5 ∧ p3) → (p4 → p4))) → False) → ((((p4 ∨ p3) → (True ∧ False)) → ((p5 ∧ p6) → (p0 ∧ p1))) → (((p0 → False) ∧ (p2 ∧ p0)) ∧ ((p5 ∧ p6) → (p2 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  intro assump_3
  have assump_61 : (((p2 → p4) → (False → False)) ∨ ((p5 ∧ p3) → (p4 → p4))) := by
    apply Or.inl
    intro assump_11
    intro assump_12
    apply False.elim assump_12
  let assump_10 := assump_1 assump_61
  apply False.elim assump_10
  apply And.intro
  have assump_62 : (((p2 → p4) → (False → False)) ∨ ((p5 ∧ p3) → (p4 → p4))) := by
    apply Or.inl
    intro assump_23
    intro assump_24
    apply False.elim assump_24
  let assump_22 := assump_1 assump_62
  apply False.elim assump_22
  have assump_63 : (((p2 → p4) → (False → False)) ∨ ((p5 ∧ p3) → (p4 → p4))) := by
    apply Or.inl
    intro assump_35
    intro assump_36
    apply False.elim assump_36
  let assump_34 := assump_1 assump_63
  apply False.elim assump_34
  intro assump_42
  cases assump_42
  case intro assump_43 assump_44 =>
    have assump_64 : (((p2 → p4) → (False → False)) ∨ ((p5 ∧ p3) → (p4 → p4))) := by
      apply Or.inl
      intro assump_54
      intro assump_55
      apply False.elim assump_55
    let assump_53 := assump_1 assump_64
    apply False.elim assump_53


variable (p2 p0 p4 p5 p3 p1 p6 : Prop)
theorem file15_101359 : ((((((p4 → p3) → False) → False) → False) ∧ ((((p0 → False) ∧ (p5 ∨ p4)) → ((p2 ∧ p6) → (True ∨ p1))) → False)) → False) := by
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    have assump_72 : (((p0 → False) ∧ (p5 ∨ p4)) → ((p2 ∧ p6) → (True ∨ p1))) := by
      intro assump_51
      intro assump_52
      cases assump_52
      case intro assump_53 assump_54 =>
        cases assump_51
        case intro assump_59 assump_60 =>
          cases assump_60
          case inl assump_63 =>
            apply Or.inl
            apply True.intro
          case inr assump_64 =>
            apply Or.inl
            apply True.intro
    let assump_50 := assump_45 assump_72
    apply False.elim assump_50


variable (p4 p0 p3 p6 p5 p2 : Prop)
theorem file15_102144 : (((((p2 → p6) ∧ (p2 → False)) ∧ ((p3 → p4) → False)) → (((False → False) ∨ (p0 → p4)) ∨ ((p4 ∨ p6) ∧ (p4 ∧ p2)))) → ((((True → False) ∧ (False ∨ False)) → ((p4 ∧ p3) → (False → False))) → (((p2 → p2) ∧ (p2 → False)) → ((p5 → False) → (p4 ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    apply Or.inr
    apply True.intro


variable (p5 p0 p1 p4 : Prop)
theorem file15_102611 : (((((p1 ∧ p1) → (p4 → False)) → ((p0 ∧ p5) ∨ (False → p0))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p1 ∧ p1) → (p4 → False)) → ((p0 ∧ p5) ∨ (False → p0))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p6 p1 p2 p7 p4 p3 : Prop)
theorem file15_103008 : (((((p4 ∧ True) ∧ (p5 → False)) → False) → (((p2 ∧ p3) ∧ (p7 → False)) ∧ ((p5 → False) ∨ (p2 → p6)))) → ((((False ∧ p1) → False) ∨ ((True → p5) → (p4 → False))) ∨ (((p6 → False) → (p4 ∨ False)) → ((p3 → False) ∧ (True ∨ False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p0 p2 p6 p7 p5 : Prop)
theorem file15_103447 : (((((p2 → False) ∨ (p2 → False)) → ((p7 ∧ False) → (p5 ∨ True))) → False) → ((((p6 ∨ p5) ∧ (p6 ∧ p0)) → False) → (((p2 ∨ p5) → (False → False)) → ((p2 → False) ∨ (p5 ∨ False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inl
  intro assump_10
  have assump_26 : (((p2 → False) ∨ (p2 → False)) → ((p7 ∧ False) → (p5 ∨ True))) := by
    intro assump_15
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply False.elim assump_18
  let assump_14 := assump_1 assump_26
  apply False.elim assump_14


variable (p5 p4 p0 p3 p7 p2 : Prop)
theorem file15_104062 : (((((p7 ∨ p5) ∨ (p0 → p0)) ∧ ((p5 ∧ p5) → False)) → (((True ∨ p4) → (True ∨ True)) ∨ ((False → False) → (p4 → False)))) → ((((p3 → p3) → False) → False) ∨ (((p3 ∨ p4) → (p7 → False)) → ((True ∨ p2) ∨ (p3 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (p3 → p3) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p1 p7 p3 p0 : Prop)
theorem file15_104526 : (((((p7 ∧ p0) ∨ (p0 → p3)) → False) ∧ (((False ∧ False) ∧ (p1 → False)) ∧ ((p7 → p3) ∨ (p3 → True)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_14


variable (p4 p2 p3 p7 p0 p1 p5 : Prop)
theorem file15_104996 : (((((p2 ∧ True) → (p2 → False)) ∨ ((p0 → p1) → (p4 → False))) → False) → ((((p1 → False) → (True ∨ False)) ∧ ((p5 → True) ∨ (True → p3))) ∧ (((p2 → False) → False) ∨ ((p2 ∧ p7) → (False ∧ True))))) := by
  intro assump_5
  apply And.intro
  apply And.intro
  intro assump_6
  apply Or.inl
  apply True.intro
  apply Or.inl
  intro assump_13
  apply True.intro
  apply Or.inl
  intro assump_16
  have assump_40 : (((p2 ∧ True) → (p2 → False)) ∨ ((p0 → p1) → (p4 → False))) := by
    apply Or.inl
    intro assump_21
    intro assump_22
    cases assump_21
    case intro assump_25 assump_26 =>
      have assump_41 : p2 := by
        exact assump_25
      let assump_33 := assump_16 assump_41
      apply False.elim assump_33
  let assump_20 := assump_5 assump_40
  apply False.elim assump_20


variable (p5 p7 p0 p6 p4 p3 p2 p1 : Prop)
theorem file15_105854 : (((((p7 ∨ p5) ∧ (p2 ∨ p5)) ∧ ((p0 → p5) ∨ (p6 → False))) ∧ (((p5 → False) ∧ (True ∨ p5)) ∨ ((p0 ∧ p1) ∨ (p2 → p4)))) ∨ ((((p3 → False) ∨ (p3 ∧ p3)) ∨ ((p6 → False) ∧ (p2 → False))) → (((p7 → p6) → (True ∨ p1)) ∨ ((p4 → False) → False)))) := by
  apply Or.inr
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      apply Or.inl
      intro assump_12
      apply Or.inl
      apply True.intro
    case inr assump_9 =>
      cases assump_9
      case intro assump_15 assump_16 =>
        apply Or.inl
        intro assump_21
        apply Or.inl
        apply True.intro
  case inr assump_7 =>
    cases assump_7
    case intro assump_24 assump_25 =>
      apply Or.inl
      intro assump_30
      apply Or.inl
      apply True.intro


variable (p7 p3 p2 p0 p5 p4 p6 : Prop)
theorem file15_106700 : (((((False → False) ∨ (p0 ∧ p7)) → False) → (((p3 ∧ p4) → False) ∧ ((p7 → False) ∨ (p7 → False)))) ∧ ((((p3 ∧ p7) ∧ (True ∨ p6)) ∧ ((p5 → False) ∧ (False ∧ p3))) → (((False ∧ p5) → False) ∨ ((True → p2) → False)))) := by
  apply And.intro
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_64 : ((False → False) ∨ (p0 ∧ p7)) := by
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_1 assump_64
    apply False.elim assump_11
  apply Or.inl
  intro assump_20
  have assump_65 : ((False → False) ∨ (p0 ∧ p7)) := by
    apply Or.inl
    intro assump_25
    apply False.elim assump_25
  let assump_24 := assump_1 assump_65
  apply False.elim assump_24
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    cases assump_32
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        cases assump_35
        case inl assump_42 =>
          cases assump_33
          case intro assump_46 assump_47 =>
            cases assump_47
            case intro assump_50 assump_51 =>
              apply False.elim assump_50
        case inr assump_43 =>
          cases assump_33
          case intro assump_56 assump_57 =>
            cases assump_57
            case intro assump_60 assump_61 =>
              apply False.elim assump_60


variable (p0 p4 p2 p1 p6 : Prop)
theorem file15_108170 : ((((((p1 ∨ p6) ∧ (p4 ∧ False)) ∧ ((p4 ∨ p6) ∧ (p4 → False))) → (((True ∧ p1) ∨ (p0 → False)) ∨ ((p2 → False) → (p0 → p6)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p1 ∨ p6) ∧ (p4 ∧ False)) ∧ ((p4 ∨ p6) ∧ (p4 → False))) → (((True ∧ p1) ∨ (p0 → False)) ∨ ((p2 → False) → (p0 → p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
        case inr assump_11 =>
          cases assump_9
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p2 p4 p3 p6 p7 p5 : Prop)
theorem file15_109039 : (((((p4 ∧ p3) → False) ∧ ((p6 ∧ True) ∧ (True ∧ p7))) → (((p3 ∨ p6) ∨ (p3 ∧ p2)) → ((p4 ∧ p3) ∨ (p6 ∨ p2)))) ∨ ((((p5 → False) ∨ (True → False)) → False) ∧ (((p4 ∨ p6) → False) ∧ ((p3 ∧ False) ∨ (p7 → p3))))) := by
  apply Or.inl
  intro assump_14
  intro assump_15
  cases assump_15
  case inl assump_16 =>
    cases assump_16
    case inl assump_18 =>
      cases assump_14
      case intro assump_22 assump_23 =>
        cases assump_23
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            cases assump_27
            case intro assump_34 assump_35 =>
              apply Or.inr
              apply Or.inl
              exact assump_28
    case inr assump_19 =>
      cases assump_14
      case intro assump_42 assump_43 =>
        cases assump_43
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_47
            case intro assump_54 assump_55 =>
              apply Or.inr
              apply Or.inl
              exact assump_48
  case inr assump_17 =>
    cases assump_17
    case intro assump_60 assump_61 =>
      cases assump_14
      case intro assump_66 assump_67 =>
        cases assump_67
        case intro assump_70 assump_71 =>
          cases assump_70
          case intro assump_72 assump_73 =>
            cases assump_71
            case intro assump_78 assump_79 =>
              apply Or.inr
              apply Or.inl
              exact assump_72


variable (p0 p5 p3 p2 p1 p7 : Prop)
theorem file15_110629 : (((((True ∨ p1) ∧ (True ∨ p1)) → ((p5 → False) → False)) ∧ (((p0 ∨ p7) ∧ (p3 ∨ True)) ∧ ((p1 ∨ True) → (p3 → False)))) → ((((p3 ∧ p1) ∧ (p2 → p0)) ∧ ((p2 → False) → (p0 ∨ p5))) → False)) := by
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
          cases assump_18
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_23
              case inl assump_25 =>
                cases assump_24
                case inl assump_29 =>
                  have assump_71 : (p1 ∨ True) := by
                    apply Or.inl
                    exact assump_8
                  let assump_35 := assump_22 assump_71
                  have assump_72 : p3 := by
                    exact assump_29
                  let assump_36 := assump_35 assump_72
                  apply False.elim assump_36
                case inr assump_30 =>
                  have assump_73 : (p1 ∨ True) := by
                    apply Or.inl
                    exact assump_8
                  let assump_44 := assump_22 assump_73
                  have assump_74 : p3 := by
                    exact assump_7
                  let assump_45 := assump_44 assump_74
                  apply False.elim assump_45
              case inr assump_26 =>
                cases assump_24
                case inl assump_51 =>
                  have assump_75 : (p1 ∨ True) := by
                    apply Or.inl
                    exact assump_8
                  let assump_57 := assump_22 assump_75
                  have assump_76 : p3 := by
                    exact assump_51
                  let assump_58 := assump_57 assump_76
                  apply False.elim assump_58
                case inr assump_52 =>
                  have assump_77 : (p1 ∨ True) := by
                    apply Or.inl
                    exact assump_8
                  let assump_66 := assump_22 assump_77
                  have assump_78 : p3 := by
                    exact assump_7
                  let assump_67 := assump_66 assump_78
                  apply False.elim assump_67


variable (p6 p1 p3 p5 p7 p2 : Prop)
theorem file15_113030 : ((((((True → True) ∨ (False ∨ p3)) → False) ∧ (((p1 → p7) ∧ (False ∧ p2)) ∧ ((p7 → p3) → False))) ∧ ((((p7 → False) → (False ∧ p6)) ∧ ((p7 → p3) ∨ (p5 ∨ p6))) → False)) → False) := by
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
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p5 p4 p2 p6 p0 p1 : Prop)
theorem file15_113630 : ((((((p0 → False) ∧ (p5 ∧ p2)) → False) ∧ (((p6 ∧ p4) → (p1 ∨ p5)) → False)) ∧ ((((False ∧ True) ∧ (p6 → p4)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : (((False ∧ True) ∧ (p6 → p4)) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p1 p6 : Prop)
theorem file15_114287 : (((((p1 → False) ∨ (p6 → False)) → ((p1 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p1 → False) ∨ (p6 → False)) → ((p1 ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p5 p6 p3 p0 p2 p1 : Prop)
theorem file15_114722 : (((((p1 → p5) ∨ (p0 → p5)) → ((False ∧ p1) ∨ (p6 ∨ True))) ∧ (((True → False) → False) ∨ ((p5 → False) → (False → False)))) ∨ ((((p6 ∧ p5) ∧ (False → True)) ∨ ((True → False) ∧ (p5 ∧ p2))) ∨ (((True ∨ p6) → (p3 → p2)) ∧ ((p7 → p5) ∧ (p6 ∨ True))))) := by
  apply Or.inl
  apply And.intro
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    apply Or.inr
    apply Or.inr
    apply True.intro
  case inr assump_7 =>
    apply Or.inr
    apply Or.inr
    apply True.intro
  apply Or.inl
  intro assump_12
  have assump_19 : True := by
    apply True.intro
  let assump_15 := assump_12 assump_19
  apply False.elim assump_15


variable (p1 p2 p7 p5 p4 p6 : Prop)
theorem file15_115412 : ((((((True → False) → (p1 ∧ True)) ∨ ((p7 ∨ p4) → False)) ∨ (((p6 → p2) ∧ (p5 ∧ p1)) ∨ ((p7 → False) ∨ (p4 ∧ True)))) → False) → False) := by
  intro assump_47
  have assump_61 : ((((True → False) → (p1 ∧ True)) ∨ ((p7 ∨ p4) → False)) ∨ (((p6 → p2) ∧ (p5 ∧ p1)) ∨ ((p7 → False) ∨ (p4 ∧ True)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_51
    apply And.intro
    have assump_62 : True := by
      apply True.intro
    let assump_54 := assump_51 assump_62
    apply False.elim assump_54
    apply True.intro
  let assump_50 := assump_47 assump_61
  apply False.elim assump_50


variable (p1 p5 p2 p6 p3 p0 p4 : Prop)
theorem file15_116066 : (((((p3 → p4) ∧ (p4 → False)) ∧ ((p2 ∧ p4) ∧ (p5 ∧ p5))) → (((p2 → False) → (p3 → p4)) → ((False → False) ∧ (p3 ∧ p1)))) ∨ ((((p3 → p1) ∧ (p0 ∧ p6)) → False) → (((p4 → False) → False) ∧ ((p6 → p4) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  apply And.intro
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_9
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_17
          case intro assump_24 assump_25 =>
            have assump_70 : p4 := by
              exact assump_19
            let assump_34 := assump_11 assump_70
            apply False.elim assump_34
  cases assump_1
  case intro assump_40 assump_41 =>
    cases assump_40
    case intro assump_42 assump_43 =>
      cases assump_41
      case intro assump_48 assump_49 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_49
          case intro assump_56 assump_57 =>
            have assump_71 : p4 := by
              exact assump_51
            let assump_66 := assump_43 assump_71
            apply False.elim assump_66


variable (p7 p3 p5 p4 : Prop)
theorem file15_117391 : (((((p4 → p7) ∧ (p5 → False)) → ((p5 ∧ True) → (p3 → False))) → False) → False) := by
  intro assump_1
  have assump_29 : (((p4 → p7) ∧ (p5 → False)) → ((p5 ∧ True) → (p3 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        have assump_30 : p5 := by
          exact assump_10
        let assump_22 := assump_17 assump_30
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p1 p2 : Prop)
theorem file15_118010 : (((((True → p1) → False) ∨ ((p7 → True) → (p2 ∨ True))) ∧ (((False → False) → (p1 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_26 : ((False → False) → (p1 → True)) := by
        intro assump_11
        intro assump_12
        apply True.intro
      let assump_10 := assump_3 assump_26
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_27 : ((False → False) → (p1 → True)) := by
        intro assump_21
        intro assump_22
        apply True.intro
      let assump_20 := assump_3 assump_27
      apply False.elim assump_20


