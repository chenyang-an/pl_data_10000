variable (p7 p2 p3 p6 : Prop)
theorem file78_38 : ((((((p3 → p7) → False) → False) → (((p6 → False) → False) → ((p3 → p3) ∨ (p2 ∨ p6)))) → False) → False) := by
  intro assump_19
  have assump_35 : ((((p3 → p7) → False) → False) → (((p6 → False) → False) → ((p3 → p3) ∨ (p2 ∨ p6)))) := by
    intro assump_23
    intro assump_24
    apply Or.inl
    intro assump_29
    exact assump_29
  let assump_22 := assump_19 assump_35
  apply False.elim assump_22


variable (p0 p5 : Prop)
theorem file78_490 : (((((True → False) → False) → False) ∨ (((p5 ∧ p5) ∨ (p0 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_24 : ((True → False) → False) := by
      intro assump_7
      have assump_25 : True := by
        apply True.intro
      let assump_10 := assump_7 assump_25
      apply False.elim assump_10
    let assump_6 := assump_2 assump_24
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_26 : ((p5 ∧ p5) ∨ (p0 → True)) := by
      apply Or.inr
      intro assump_20
      apply True.intro
    let assump_19 := assump_3 assump_26
    apply False.elim assump_19


variable (p1 p2 p0 p5 p7 p6 : Prop)
theorem file78_1185 : (((((False ∨ p2) → (p5 → False)) → ((True → False) → (p6 ∨ True))) ∨ (((p0 ∨ p7) → False) ∨ ((p0 ∧ p6) → (p6 → p0)))) ∨ ((((p6 ∨ p1) → False) → False) ∨ (((p2 ∧ p6) → (p6 → False)) ∧ ((False → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  apply True.intro


variable (p7 p0 p4 p6 p3 p5 p1 : Prop)
theorem file78_1564 : ((((((True → False) ∨ (True → False)) ∧ ((p4 → p4) ∨ (p0 → p7))) → (((p3 → p6) ∧ (p7 → p5)) → ((p3 → False) → False))) → ((((p0 ∨ p0) ∨ (p0 → True)) → False) ∧ (((p3 ∧ p3) → False) ∧ ((True ∧ p1) → False)))) → False) := by
  intro assump_1
  have assump_62 : ((((True → False) ∨ (True → False)) ∧ ((p4 → p4) ∨ (p0 → p7))) → (((p3 → p6) ∧ (p7 → p5)) → ((p3 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_17
          case inl assump_22 =>
            have assump_63 : True := by
              apply True.intro
            let assump_27 := assump_18 assump_63
            apply False.elim assump_27
          case inr assump_23 =>
            have assump_64 : True := by
              apply True.intro
            let assump_34 := assump_18 assump_64
            apply False.elim assump_34
        case inr assump_19 =>
          cases assump_17
          case inl assump_40 =>
            have assump_65 : True := by
              apply True.intro
            let assump_45 := assump_19 assump_65
            apply False.elim assump_45
          case inr assump_41 =>
            have assump_66 : True := by
              apply True.intro
            let assump_52 := assump_19 assump_66
            apply False.elim assump_52
  let assump_4 := assump_1 assump_62
  let assump_56 := And.left assump_4
  have assump_67 : ((p0 ∨ p0) ∨ (p0 → True)) := by
    apply Or.inr
    intro assump_58
    apply True.intro
  let assump_57 := assump_56 assump_67
  apply False.elim assump_57


variable (p7 p1 p6 p0 p2 p4 : Prop)
theorem file78_3332 : (((((p7 → p0) → False) ∧ ((p0 ∨ p7) ∧ (p0 ∧ p2))) → (((p1 → p0) ∧ (p1 ∧ p1)) ∧ ((True → False) ∨ (p4 → p2)))) ∨ ((((p0 → False) ∧ (p6 ∨ True)) ∨ ((p6 ∨ p6) → (p1 ∨ p7))) → (((p2 ∨ p4) ∧ (False → p2)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          exact assump_15
      case inr assump_12 =>
        cases assump_10
        case intro assump_23 assump_24 =>
          exact assump_23
  apply And.intro
  cases assump_1
  case intro assump_29 assump_30 =>
    cases assump_30
    case intro assump_33 assump_34 =>
      cases assump_33
      case inl assump_35 =>
        cases assump_34
        case intro assump_39 assump_40 =>
          have assump_167 : (p7 → p0) := by
            intro assump_49
            exact assump_39
          let assump_48 := assump_29 assump_167
          apply False.elim assump_48
      case inr assump_36 =>
        cases assump_34
        case intro assump_57 assump_58 =>
          have assump_168 : (p7 → p0) := by
            intro assump_67
            exact assump_57
          let assump_66 := assump_29 assump_168
          apply False.elim assump_66
  cases assump_1
  case intro assump_73 assump_74 =>
    cases assump_74
    case intro assump_77 assump_78 =>
      cases assump_77
      case inl assump_79 =>
        cases assump_78
        case intro assump_83 assump_84 =>
          have assump_169 : (p7 → p0) := by
            intro assump_93
            exact assump_83
          let assump_92 := assump_73 assump_169
          apply False.elim assump_92
      case inr assump_80 =>
        cases assump_78
        case intro assump_101 assump_102 =>
          have assump_170 : (p7 → p0) := by
            intro assump_111
            exact assump_101
          let assump_110 := assump_73 assump_170
          apply False.elim assump_110
  cases assump_1
  case intro assump_117 assump_118 =>
    cases assump_118
    case intro assump_121 assump_122 =>
      cases assump_121
      case inl assump_123 =>
        cases assump_122
        case intro assump_127 assump_128 =>
          apply Or.inl
          intro assump_133
          have assump_171 : (p7 → p0) := by
            intro assump_140
            exact assump_127
          let assump_139 := assump_117 assump_171
          apply False.elim assump_139
      case inr assump_124 =>
        cases assump_122
        case intro assump_148 assump_149 =>
          apply Or.inl
          intro assump_154
          have assump_172 : (p7 → p0) := by
            intro assump_161
            exact assump_148
          let assump_160 := assump_117 assump_172
          apply False.elim assump_160


variable (p3 p1 p6 : Prop)
theorem file78_6274 : (((((True ∨ p3) → False) → False) ∨ (((True → False) → False) → False)) ∨ ((((p3 ∧ p1) → False) → ((p1 → False) ∨ (p3 → p1))) → (((True → False) → False) ∨ ((p6 → False) → (p1 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_10
  have assump_17 : (True ∨ p3) := by
    apply Or.inl
    apply True.intro
  let assump_13 := assump_10 assump_17
  apply False.elim assump_13


variable (p0 p3 p4 p2 : Prop)
theorem file78_6714 : ((((((False → p2) → False) → ((True ∨ False) ∧ (p3 → p4))) ∨ (((p4 → False) → False) ∧ ((p4 → p3) ∧ (p0 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → p2) → False) → ((True ∨ False) ∧ (p3 → p4))) ∨ (((p4 → False) → False) ∧ ((p4 → p3) ∧ (p0 ∧ p3)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_8
    have assump_24 : (False → p2) := by
      intro assump_14
      apply False.elim assump_14
    let assump_13 := assump_5 assump_24
    apply False.elim assump_13
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p1 p7 p6 p5 p0 p4 : Prop)
theorem file78_7408 : (((((p4 → False) ∧ (p1 ∧ p5)) ∨ ((True ∧ p0) → False)) ∧ (((p1 ∨ p7) ∨ (p6 ∨ p1)) → False)) → ((((p0 → True) ∨ (p7 ∧ False)) ∨ ((p5 ∨ p1) ∨ (True ∨ p5))) ∧ (((p6 → p0) → False) → False))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply Or.inl
          apply Or.inl
          intro assump_18
          apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_23
      apply True.intro
  intro assump_24
  cases assump_1
  case intro assump_27 assump_28 =>
    cases assump_27
    case inl assump_29 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_32
        case intro assump_35 assump_36 =>
          have assump_65 : ((p1 ∨ p7) ∨ (p6 ∨ p1)) := by
            apply Or.inl
            apply Or.inl
            exact assump_35
          let assump_43 := assump_28 assump_65
          apply False.elim assump_43
    case inr assump_30 =>
      have assump_66 : (p6 → p0) := by
        intro assump_54
        have assump_67 : ((p1 ∨ p7) ∨ (p6 ∨ p1)) := by
          apply Or.inr
          apply Or.inl
          exact assump_54
        let assump_58 := assump_28 assump_67
        apply False.elim assump_58
      let assump_53 := assump_24 assump_66
      apply False.elim assump_53


variable (p5 p0 p1 p4 p2 p3 : Prop)
theorem file78_8959 : (((((True → p5) ∧ (p1 ∧ False)) ∧ ((False ∨ True) → (True ∧ p5))) ∧ (((True → p4) ∧ (p3 ∨ p2)) ∨ ((p3 → False) → (p0 ∨ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_11


variable (p6 p4 p5 p2 p7 p0 : Prop)
theorem file78_9444 : ((((((p4 ∧ p2) ∧ (True → False)) → ((p4 ∧ p4) → False)) → False) ∧ ((((p0 ∧ p4) ∧ (p6 ∨ p6)) ∧ ((p5 → p0) ∧ (p2 ∧ p6))) → (((p0 ∧ False) → False) ∨ ((p2 ∧ p7) ∧ (p5 → False))))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    have assump_53 : (((p4 ∧ p2) ∧ (True → False)) → ((p4 ∧ p4) → False)) := by
      intro assump_28
      intro assump_29
      cases assump_29
      case intro assump_30 assump_31 =>
        cases assump_28
        case intro assump_36 assump_37 =>
          cases assump_36
          case intro assump_38 assump_39 =>
            have assump_54 : True := by
              apply True.intro
            let assump_46 := assump_37 assump_54
            apply False.elim assump_46
    let assump_27 := assump_20 assump_53
    apply False.elim assump_27


variable (p6 p3 p7 p4 p2 p1 : Prop)
theorem file78_10322 : (((((False ∧ p3) → (p3 ∧ p3)) ∧ ((p2 ∨ False) ∨ (p7 ∨ p4))) → False) → ((((p2 → False) → False) ∧ ((p1 → False) ∨ (p7 ∧ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      have assump_66 : (p2 → False) := by
        intro assump_25
        have assump_67 : (((False ∧ p3) → (p3 ∧ p3)) ∧ ((p2 ∨ False) ∨ (p7 ∨ p4))) := by
          apply And.intro
          intro assump_30
          apply And.intro
          cases assump_30
          case intro assump_31 assump_32 =>
            apply False.elim assump_31
          cases assump_30
          case intro assump_35 assump_36 =>
            apply False.elim assump_35
          apply Or.inl
          apply Or.inl
          exact assump_25
        let assump_29 := assump_1 assump_67
        apply False.elim assump_29
      let assump_24 := assump_3 assump_66
      apply False.elim assump_24
    case inr assump_8 =>
      cases assump_8
      case intro assump_45 assump_46 =>
        have assump_68 : (((False ∧ p3) → (p3 ∧ p3)) ∧ ((p2 ∨ False) ∨ (p7 ∨ p4))) := by
          apply And.intro
          intro assump_54
          apply And.intro
          cases assump_54
          case intro assump_55 assump_56 =>
            apply False.elim assump_55
          cases assump_54
          case intro assump_59 assump_60 =>
            apply False.elim assump_59
          apply Or.inr
          apply Or.inl
          exact assump_45
        let assump_53 := assump_1 assump_68
        apply False.elim assump_53


variable (p1 p4 p7 p2 p0 p6 p3 p5 : Prop)
theorem file78_11958 : (((((False ∨ p3) → (p4 ∨ p3)) → False) → False) ∨ ((((p7 ∨ p6) ∨ (p2 ∧ p1)) → ((p4 ∧ p0) → (True ∧ p5))) ∨ (((p2 ∧ p1) ∨ (p4 → p5)) → ((p4 ∧ p3) ∧ (p4 ∧ p0))))) := by
  apply Or.inl
  intro assump_5
  have assump_19 : ((False ∨ p3) → (p4 ∨ p3)) := by
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      apply Or.inr
      exact assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p6 p5 p0 : Prop)
theorem file78_12489 : (((((p0 ∨ True) → False) → ((p5 → False) → (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_21 : (((p0 ∨ True) → False) → ((p5 → False) → (p6 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_22 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_14 := assump_5 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p6 p7 p4 p3 p2 : Prop)
theorem file78_13003 : ((((((p6 ∧ p3) ∧ (True ∧ False)) → False) ∨ (((False ∨ p2) ∨ (p7 → False)) → False)) ∧ ((((False ∨ p2) ∧ (p7 ∧ False)) ∧ ((p4 ∨ False) ∧ (p0 ∧ p0))) ∧ (((p7 → False) → False) ∧ ((p6 → True) ∨ (p0 → True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              apply False.elim assump_14
            case inr assump_15 =>
              cases assump_13
              case intro assump_20 assump_21 =>
                apply False.elim assump_21
    case inr assump_5 =>
      cases assump_3
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_32
            case inl assump_34 =>
              apply False.elim assump_34
            case inr assump_35 =>
              cases assump_33
              case intro assump_40 assump_41 =>
                apply False.elim assump_41


variable (p7 p2 p3 p6 p1 p0 : Prop)
theorem file78_14330 : ((((((p2 ∧ p7) → (p0 ∨ p3)) → False) → (((True ∧ False) → False) → ((p1 → p6) → (False → p7)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 ∧ p7) → (p0 ∨ p3)) → False) → (((True ∧ False) → False) → ((p1 → p6) → (False → p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p0 p5 p2 : Prop)
theorem file78_14811 : (((((p5 ∨ False) → False) → ((p0 → False) ∧ (p2 ∧ p5))) ∧ (((p7 → True) ∨ (True ∧ p5)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p7 → True) ∨ (True ∧ p5)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p5 p2 p0 p7 p1 p3 p6 p4 : Prop)
theorem file78_15244 : ((((((p0 → p6) → False) → False) ∧ (((p4 ∧ p7) ∨ (True → True)) ∨ ((p4 ∧ p5) ∧ (True ∨ True)))) ∧ ((((p7 → p7) ∨ (p7 → False)) → False) ∧ (((p1 → False) ∧ (p6 ∧ p3)) ∧ ((p0 ∧ p2) → (p2 → False))))) → False) := by
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    cases assump_34
    case intro assump_36 assump_37 =>
      cases assump_37
      case inl assump_40 =>
        cases assump_40
        case inl assump_42 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            cases assump_35
            case intro assump_50 assump_51 =>
              cases assump_51
              case intro assump_54 assump_55 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  cases assump_57
                  case intro assump_60 assump_61 =>
                    have assump_182 : ((p7 → p7) ∨ (p7 → False)) := by
                      apply Or.inl
                      intro assump_73
                      exact assump_73
                    let assump_72 := assump_50 assump_182
                    apply False.elim assump_72
        case inr assump_43 =>
          cases assump_35
          case intro assump_81 assump_82 =>
            cases assump_82
            case intro assump_85 assump_86 =>
              cases assump_85
              case intro assump_87 assump_88 =>
                cases assump_88
                case intro assump_91 assump_92 =>
                  have assump_183 : ((p7 → p7) ∨ (p7 → False)) := by
                    apply Or.inl
                    intro assump_104
                    exact assump_104
                  let assump_103 := assump_81 assump_183
                  apply False.elim assump_103
      case inr assump_41 =>
        cases assump_41
        case intro assump_110 assump_111 =>
          cases assump_110
          case intro assump_112 assump_113 =>
            cases assump_111
            case inl assump_118 =>
              cases assump_35
              case intro assump_122 assump_123 =>
                cases assump_123
                case intro assump_126 assump_127 =>
                  cases assump_126
                  case intro assump_128 assump_129 =>
                    cases assump_129
                    case intro assump_132 assump_133 =>
                      have assump_184 : ((p7 → p7) ∨ (p7 → False)) := by
                        apply Or.inl
                        intro assump_145
                        exact assump_145
                      let assump_144 := assump_122 assump_184
                      apply False.elim assump_144
            case inr assump_119 =>
              cases assump_35
              case intro assump_153 assump_154 =>
                cases assump_154
                case intro assump_157 assump_158 =>
                  cases assump_157
                  case intro assump_159 assump_160 =>
                    cases assump_160
                    case intro assump_163 assump_164 =>
                      have assump_185 : ((p7 → p7) ∨ (p7 → False)) := by
                        apply Or.inl
                        intro assump_176
                        exact assump_176
                      let assump_175 := assump_153 assump_185
                      apply False.elim assump_175


variable (p0 p6 p1 p3 p2 p5 p4 : Prop)
theorem file78_18614 : (((((p0 ∧ p3) → (p1 ∧ True)) → ((p6 → False) → False)) ∧ (((p2 ∧ p1) → False) ∧ ((True ∨ p5) → False))) → ((((p0 → p2) ∧ (True ∨ False)) → ((p6 → False) ∨ (p4 → False))) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      have assump_27 : (True ∨ p5) := by
        apply Or.inl
        apply True.intro
      let assump_23 := assump_18 assump_27
      apply False.elim assump_23


variable (p1 p7 p2 p4 p3 p6 p5 p0 : Prop)
theorem file78_19175 : (((((False → False) → (False → p2)) ∨ ((p6 ∨ p0) ∨ (p0 ∧ p7))) ∨ (((p5 ∨ p5) → False) ∧ ((True → p3) ∧ (p6 → p0)))) ∨ ((((False → False) ∧ (p7 → False)) → ((False ∧ p1) ∨ (p6 ∨ p3))) → (((p4 ∧ p0) ∧ (False → False)) → ((False ∨ p6) ∧ (p2 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_28
  intro assump_29
  apply False.elim assump_29


variable (p2 : Prop)
theorem file78_19587 : (((((True ∨ p2) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p2) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p7 p6 p1 : Prop)
theorem file78_20007 : ((((((p3 → False) ∧ (p6 ∨ p7)) ∧ ((False → False) ∧ (True → False))) → False) → ((((True ∨ p1) ∧ (True → False)) → ((False ∨ False) ∧ (p3 → False))) → False)) → False) := by
  intro assump_1
  have assump_86 : ((((p3 → False) ∧ (p6 ∨ p7)) ∧ ((False → False) ∧ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            have assump_87 : True := by
              apply True.intro
            let assump_22 := assump_17 assump_87
            apply False.elim assump_22
        case inr assump_13 =>
          cases assump_7
          case intro assump_28 assump_29 =>
            have assump_88 : True := by
              apply True.intro
            let assump_34 := assump_29 assump_88
            apply False.elim assump_34
  let assump_4 := assump_1 assump_86
  have assump_89 : (((True ∨ p1) ∧ (True → False)) → ((False ∨ False) ∧ (p3 → False))) := by
    intro assump_39
    apply And.intro
    cases assump_39
    case intro assump_40 assump_41 =>
      cases assump_40
      case inl assump_42 =>
        have assump_90 : True := by
          apply True.intro
        let assump_48 := assump_41 assump_90
        apply False.elim assump_48
      case inr assump_43 =>
        have assump_91 : True := by
          apply True.intro
        let assump_56 := assump_41 assump_91
        apply False.elim assump_56
    intro assump_60
    cases assump_39
    case intro assump_63 assump_64 =>
      cases assump_63
      case inl assump_65 =>
        have assump_92 : True := by
          apply True.intro
        let assump_71 := assump_64 assump_92
        apply False.elim assump_71
      case inr assump_66 =>
        have assump_93 : True := by
          apply True.intro
        let assump_79 := assump_64 assump_93
        apply False.elim assump_79
  let assump_38 := assump_4 assump_89
  apply False.elim assump_38


variable (p5 p4 p0 p2 p3 : Prop)
theorem file78_22129 : ((((((p0 → p2) → (True ∨ p3)) ∨ ((p5 → p2) → False)) ∨ (((p2 ∧ False) → False) ∨ ((p4 → p2) → (False → p5)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p0 → p2) → (True ∨ p3)) ∨ ((p5 → p2) → False)) ∨ (((p2 ∧ False) → False) ∨ ((p4 → p2) → (False → p5)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p6 p1 p3 p0 p4 p5 : Prop)
theorem file78_22632 : (((((True ∨ p6) ∧ (p2 → False)) → ((p2 → p0) ∧ (True ∨ p6))) → False) → ((((p2 → False) → (p6 → p5)) ∧ ((p4 → p1) ∧ (p3 ∨ p1))) ∧ (((p4 → False) → False) ∧ ((p4 ∧ p3) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  have assump_231 : (((True ∨ p6) ∧ (p2 → False)) → ((p2 → p0) ∧ (True ∨ p6))) := by
    intro assump_11
    apply And.intro
    intro assump_12
    cases assump_11
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        have assump_232 : p2 := by
          exact assump_12
        let assump_23 := assump_16 assump_232
        apply False.elim assump_23
      case inr assump_18 =>
        have assump_233 : p2 := by
          exact assump_12
        let assump_31 := assump_16 assump_233
        apply False.elim assump_31
    cases assump_11
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        apply Or.inl
        apply True.intro
      case inr assump_38 =>
        apply Or.inl
        apply True.intro
  let assump_10 := assump_1 assump_231
  apply False.elim assump_10
  apply And.intro
  intro assump_50
  have assump_234 : (((True ∨ p6) ∧ (p2 → False)) → ((p2 → p0) ∧ (True ∨ p6))) := by
    intro assump_56
    apply And.intro
    intro assump_57
    cases assump_56
    case intro assump_60 assump_61 =>
      cases assump_60
      case inl assump_62 =>
        have assump_235 : p2 := by
          exact assump_57
        let assump_68 := assump_61 assump_235
        apply False.elim assump_68
      case inr assump_63 =>
        have assump_236 : p2 := by
          exact assump_57
        let assump_76 := assump_61 assump_236
        apply False.elim assump_76
    cases assump_56
    case intro assump_80 assump_81 =>
      cases assump_80
      case inl assump_82 =>
        apply Or.inl
        apply True.intro
      case inr assump_83 =>
        apply Or.inl
        apply True.intro
  let assump_55 := assump_1 assump_234
  apply False.elim assump_55
  have assump_237 : (((True ∨ p6) ∧ (p2 → False)) → ((p2 → p0) ∧ (True ∨ p6))) := by
    intro assump_98
    apply And.intro
    intro assump_99
    cases assump_98
    case intro assump_102 assump_103 =>
      cases assump_102
      case inl assump_104 =>
        have assump_238 : p2 := by
          exact assump_99
        let assump_110 := assump_103 assump_238
        apply False.elim assump_110
      case inr assump_105 =>
        have assump_239 : p2 := by
          exact assump_99
        let assump_118 := assump_103 assump_239
        apply False.elim assump_118
    cases assump_98
    case intro assump_122 assump_123 =>
      cases assump_122
      case inl assump_124 =>
        apply Or.inl
        apply True.intro
      case inr assump_125 =>
        apply Or.inl
        apply True.intro
  let assump_97 := assump_1 assump_237
  apply False.elim assump_97
  apply And.intro
  intro assump_137
  have assump_240 : (((True ∨ p6) ∧ (p2 → False)) → ((p2 → p0) ∧ (True ∨ p6))) := by
    intro assump_143
    apply And.intro
    intro assump_144
    cases assump_143
    case intro assump_147 assump_148 =>
      cases assump_147
      case inl assump_149 =>
        have assump_241 : p2 := by
          exact assump_144
        let assump_155 := assump_148 assump_241
        apply False.elim assump_155
      case inr assump_150 =>
        have assump_242 : p2 := by
          exact assump_144
        let assump_163 := assump_148 assump_242
        apply False.elim assump_163
    cases assump_143
    case intro assump_167 assump_168 =>
      cases assump_167
      case inl assump_169 =>
        apply Or.inl
        apply True.intro
      case inr assump_170 =>
        apply Or.inl
        apply True.intro
  let assump_142 := assump_1 assump_240
  apply False.elim assump_142
  intro assump_182
  cases assump_182
  case intro assump_183 assump_184 =>
    have assump_243 : (((True ∨ p6) ∧ (p2 → False)) → ((p2 → p0) ∧ (True ∨ p6))) := by
      intro assump_192
      apply And.intro
      intro assump_193
      cases assump_192
      case intro assump_196 assump_197 =>
        cases assump_196
        case inl assump_198 =>
          have assump_244 : p2 := by
            exact assump_193
          let assump_204 := assump_197 assump_244
          apply False.elim assump_204
        case inr assump_199 =>
          have assump_245 : p2 := by
            exact assump_193
          let assump_212 := assump_197 assump_245
          apply False.elim assump_212
      cases assump_192
      case intro assump_216 assump_217 =>
        cases assump_216
        case inl assump_218 =>
          apply Or.inl
          apply True.intro
        case inr assump_219 =>
          apply Or.inl
          apply True.intro
    let assump_191 := assump_1 assump_243
    apply False.elim assump_191


variable (p0 p1 p4 p6 p3 : Prop)
theorem file78_27535 : (((((p6 ∧ False) ∧ (True → p0)) → ((p4 ∧ p6) → (p3 → p1))) ∧ (((p4 ∧ False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p4 ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p5 p6 p0 p3 p2 p4 p1 : Prop)
theorem file78_28012 : (((((False ∨ p1) ∨ (p2 → p4)) ∧ ((p2 ∧ p2) ∧ (p1 ∨ p5))) → False) → ((((p0 ∧ False) ∨ (p6 ∨ p4)) ∨ ((p5 ∧ p3) ∨ (p2 ∨ p3))) → (((p2 ∧ p2) → False) → ((p0 → False) → (True ∨ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    case inr assump_12 =>
      cases assump_12
      case inl assump_19 =>
        apply Or.inl
        apply True.intro
      case inr assump_20 =>
        apply Or.inl
        apply True.intro
  case inr assump_10 =>
    cases assump_10
    case inl assump_29 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        apply Or.inl
        apply True.intro
    case inr assump_30 =>
      cases assump_30
      case inl assump_39 =>
        apply Or.inl
        apply True.intro
      case inr assump_40 =>
        apply Or.inl
        apply True.intro


variable (p1 p0 p2 p6 p7 p5 p3 : Prop)
theorem file78_29082 : ((((((True ∨ p0) → False) → ((p2 → False) ∧ (p3 → p7))) ∧ (((p3 → False) ∨ (p7 → False)) → ((p6 → False) → False))) ∧ ((((p1 ∨ p6) → (True → False)) → ((p6 → False) ∨ (p5 ∨ False))) → False)) → False) := by
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    cases assump_34
    case intro assump_36 assump_37 =>
      have assump_60 : (((p1 ∨ p6) → (True → False)) → ((p6 → False) ∨ (p5 ∨ False))) := by
        intro assump_45
        apply Or.inl
        intro assump_48
        have assump_61 : (p1 ∨ p6) := by
          apply Or.inr
          exact assump_48
        let assump_52 := assump_45 assump_61
        have assump_62 : True := by
          apply True.intro
        let assump_53 := assump_52 assump_62
        apply False.elim assump_53
      let assump_44 := assump_35 assump_60
      apply False.elim assump_44


variable (p6 p5 p2 p0 p3 : Prop)
theorem file78_29991 : ((((((p0 ∧ p5) ∧ (p0 ∧ p2)) → False) → (((p3 ∧ p5) ∧ (p6 → False)) → ((p3 ∨ p0) → (p3 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p0 ∧ p5) ∧ (p0 ∧ p2)) → False) → (((p3 ∧ p5) ∧ (p6 → False)) → ((p3 ∨ p0) → (p3 → True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p4 p3 p0 p2 : Prop)
theorem file78_30468 : (((((p1 → False) → (p0 → p2)) → ((p4 ∨ p0) → (p3 → p3))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p1 → False) → (p0 → p2)) → ((p4 ∨ p0) → (p3 → p3))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      exact assump_7
    case inr assump_11 =>
      exact assump_7
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 : Prop)
theorem file78_30926 : (((((p2 → p2) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((p2 → p2) → False) → False) := by
    intro assump_5
    have assump_19 : (p2 → p2) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p3 p7 p5 p4 p1 p6 : Prop)
theorem file78_31349 : (((((False → p7) → (p6 ∨ p4)) ∧ ((p7 → p1) ∨ (p5 ∧ p0))) → False) → ((((p0 → False) → (True → p3)) → False) → (((False ∨ p0) ∨ (True ∨ p5)) ∨ ((p3 ∧ p4) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p0 p7 p2 p5 p4 p6 p1 p3 : Prop)
theorem file78_31684 : (((((p3 ∨ p7) ∧ (p4 ∨ p6)) ∧ ((p0 ∧ p1) → (p7 → False))) → (((p3 ∨ p3) → False) ∧ ((False ∧ p4) ∧ (p2 ∧ p6)))) → ((((p1 ∨ p5) ∨ (p6 ∨ p0)) → False) → (((p6 → False) ∨ (p7 → False)) ∨ ((True ∧ True) → (p7 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  intro assump_7
  have assump_16 : ((p1 ∨ p5) ∨ (p6 ∨ p0)) := by
    apply Or.inr
    apply Or.inl
    exact assump_7
  let assump_12 := assump_2 assump_16
  apply False.elim assump_12


variable (p7 p0 p4 p5 p2 p6 : Prop)
theorem file78_32217 : (((((p0 ∧ p4) → False) ∧ ((p2 → p6) ∨ (p2 → False))) ∧ (((True ∨ p7) → (False ∧ p5)) ∧ ((p0 → False) ∧ (p5 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            have assump_48 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_24 := assump_12 assump_48
            let assump_25 := And.left assump_24
            apply False.elim assump_25
      case inr assump_9 =>
        cases assump_3
        case intro assump_31 assump_32 =>
          cases assump_32
          case intro assump_35 assump_36 =>
            have assump_49 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_43 := assump_31 assump_49
            let assump_44 := And.left assump_43
            apply False.elim assump_44


variable (p5 p2 p3 p1 p0 p4 p7 : Prop)
theorem file78_33364 : (((((p3 → p2) → False) ∧ ((False ∧ p0) ∨ (p2 ∧ p3))) ∧ (((True → False) ∨ (p7 → False)) ∧ ((p4 ∨ p0) ∧ (p3 → False)))) → ((((p4 ∧ p3) ∨ (p5 → p5)) ∨ ((p1 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_16
            case inl assump_19 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                apply False.elim assump_21
            case inr assump_20 =>
              cases assump_20
              case intro assump_25 assump_26 =>
                cases assump_14
                case intro assump_31 assump_32 =>
                  cases assump_31
                  case inl assump_33 =>
                    cases assump_32
                    case intro assump_37 assump_38 =>
                      cases assump_37
                      case inl assump_39 =>
                        have assump_215 : p3 := by
                          exact assump_26
                        let assump_45 := assump_38 assump_215
                        apply False.elim assump_45
                      case inr assump_40 =>
                        have assump_216 : p3 := by
                          exact assump_26
                        let assump_53 := assump_38 assump_216
                        apply False.elim assump_53
                  case inr assump_34 =>
                    cases assump_32
                    case intro assump_59 assump_60 =>
                      cases assump_59
                      case inl assump_61 =>
                        have assump_217 : p3 := by
                          exact assump_26
                        let assump_67 := assump_60 assump_217
                        apply False.elim assump_67
                      case inr assump_62 =>
                        have assump_218 : p3 := by
                          exact assump_26
                        let assump_75 := assump_60 assump_218
                        apply False.elim assump_75
    case inr assump_6 =>
      cases assump_1
      case intro assump_81 assump_82 =>
        cases assump_81
        case intro assump_83 assump_84 =>
          cases assump_84
          case inl assump_87 =>
            cases assump_87
            case intro assump_89 assump_90 =>
              apply False.elim assump_89
          case inr assump_88 =>
            cases assump_88
            case intro assump_93 assump_94 =>
              cases assump_82
              case intro assump_99 assump_100 =>
                cases assump_99
                case inl assump_101 =>
                  cases assump_100
                  case intro assump_105 assump_106 =>
                    cases assump_105
                    case inl assump_107 =>
                      have assump_219 : p3 := by
                        exact assump_94
                      let assump_113 := assump_106 assump_219
                      apply False.elim assump_113
                    case inr assump_108 =>
                      have assump_220 : p3 := by
                        exact assump_94
                      let assump_121 := assump_106 assump_220
                      apply False.elim assump_121
                case inr assump_102 =>
                  cases assump_100
                  case intro assump_127 assump_128 =>
                    cases assump_127
                    case inl assump_129 =>
                      have assump_221 : p3 := by
                        exact assump_94
                      let assump_135 := assump_128 assump_221
                      apply False.elim assump_135
                    case inr assump_130 =>
                      have assump_222 : p3 := by
                        exact assump_94
                      let assump_143 := assump_128 assump_222
                      apply False.elim assump_143
  case inr assump_4 =>
    cases assump_1
    case intro assump_149 assump_150 =>
      cases assump_149
      case intro assump_151 assump_152 =>
        cases assump_152
        case inl assump_155 =>
          cases assump_155
          case intro assump_157 assump_158 =>
            apply False.elim assump_157
        case inr assump_156 =>
          cases assump_156
          case intro assump_161 assump_162 =>
            cases assump_150
            case intro assump_167 assump_168 =>
              cases assump_167
              case inl assump_169 =>
                cases assump_168
                case intro assump_173 assump_174 =>
                  cases assump_173
                  case inl assump_175 =>
                    have assump_223 : p3 := by
                      exact assump_162
                    let assump_181 := assump_174 assump_223
                    apply False.elim assump_181
                  case inr assump_176 =>
                    have assump_224 : p3 := by
                      exact assump_162
                    let assump_189 := assump_174 assump_224
                    apply False.elim assump_189
              case inr assump_170 =>
                cases assump_168
                case intro assump_195 assump_196 =>
                  cases assump_195
                  case inl assump_197 =>
                    have assump_225 : p3 := by
                      exact assump_162
                    let assump_203 := assump_196 assump_225
                    apply False.elim assump_203
                  case inr assump_198 =>
                    have assump_226 : p3 := by
                      exact assump_162
                    let assump_211 := assump_196 assump_226
                    apply False.elim assump_211


variable (p4 p0 : Prop)
theorem file78_39290 : ((((((True → True) ∨ (p4 → False)) ∧ ((p0 → p0) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((True → True) ∨ (p4 → False)) ∧ ((p0 → p0) → False)) → False) := by
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


variable (p0 p4 p2 p6 p7 p5 p1 p3 : Prop)
theorem file78_40112 : (((((True ∨ p7) ∨ (p4 ∧ p2)) ∨ ((True → False) → (p1 ∨ False))) ∨ (((p0 ∧ p5) ∧ (p2 ∧ p0)) ∧ ((p1 ∨ p4) ∨ (p6 ∨ p4)))) ∨ ((((p3 ∨ p7) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p3 p4 p6 p5 p1 : Prop)
theorem file78_40431 : (((((p1 ∨ p6) → (p3 → False)) ∧ ((False → p6) ∨ (p6 → False))) → False) → ((((p3 → p1) → False) → False) → (((p4 → False) → (p4 ∨ True)) ∨ ((False ∧ p5) → (False ∨ p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply Or.inr
  apply True.intro


variable (p7 p4 p6 p3 p0 p2 p5 : Prop)
theorem file78_40772 : ((((((False → False) ∧ (False ∧ p5)) ∧ ((True → p3) → (p3 → p3))) ∧ (((p5 ∨ p2) → False) ∧ ((True ∨ False) ∧ (p4 ∧ p0)))) ∧ ((((p5 → False) ∧ (p0 → False)) ∨ ((p7 ∧ p6) ∧ (p2 ∨ p7))) → False)) → False) := by
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
          case intro assump_12 assump_13 =>
            apply False.elim assump_12


variable (p4 p6 p0 p7 p3 p1 : Prop)
theorem file78_41393 : (((((True → False) ∧ (p6 ∨ p3)) → False) → False) → ((((True → False) ∨ (p1 ∧ p4)) → False) ∧ (((p7 → False) → (p7 → p6)) → ((False → False) ∧ (p0 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_103 : (((True → False) ∧ (p6 ∨ p3)) → False) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          have assump_104 : True := by
            apply True.intro
          let assump_20 := assump_11 assump_104
          apply False.elim assump_20
        case inr assump_16 =>
          have assump_105 : True := by
            apply True.intro
          let assump_27 := assump_11 assump_105
          apply False.elim assump_27
    let assump_9 := assump_1 assump_103
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case intro assump_34 assump_35 =>
      have assump_106 : (((True → False) ∧ (p6 ∨ p3)) → False) := by
        intro assump_43
        cases assump_43
        case intro assump_44 assump_45 =>
          cases assump_45
          case inl assump_48 =>
            have assump_107 : True := by
              apply True.intro
            let assump_53 := assump_44 assump_107
            apply False.elim assump_53
          case inr assump_49 =>
            have assump_108 : True := by
              apply True.intro
            let assump_60 := assump_44 assump_108
            apply False.elim assump_60
      let assump_42 := assump_1 assump_106
      apply False.elim assump_42
  intro assump_67
  apply And.intro
  intro assump_68
  apply False.elim assump_68
  intro assump_71
  have assump_109 : (((True → False) ∧ (p6 ∨ p3)) → False) := by
    intro assump_79
    cases assump_79
    case intro assump_80 assump_81 =>
      cases assump_81
      case inl assump_84 =>
        have assump_110 : True := by
          apply True.intro
        let assump_89 := assump_80 assump_110
        apply False.elim assump_89
      case inr assump_85 =>
        have assump_111 : True := by
          apply True.intro
        let assump_96 := assump_80 assump_111
        apply False.elim assump_96
  let assump_78 := assump_1 assump_109
  apply False.elim assump_78


variable (p7 p2 p4 p0 p5 p6 p3 : Prop)
theorem file78_43732 : ((((((p4 ∧ p6) ∧ (p2 → False)) → ((p4 ∨ p3) → (p6 ∧ True))) → False) ∧ ((((p6 ∧ p0) ∧ (p2 ∧ p6)) → ((p2 → p0) ∨ (p4 ∨ p5))) ∧ (((p3 → p3) → (p7 → False)) ∨ ((p6 → p7) ∧ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_93 : (((p4 ∧ p6) ∧ (p2 → False)) → ((p4 ∨ p3) → (p6 ∧ True))) := by
          intro assump_21
          intro assump_22
          apply And.intro
          cases assump_22
          case inl assump_23 =>
            cases assump_21
            case intro assump_27 assump_28 =>
              cases assump_27
              case intro assump_29 assump_30 =>
                exact assump_30
          case inr assump_24 =>
            cases assump_21
            case intro assump_39 assump_40 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                exact assump_42
          apply True.intro
        let assump_20 := assump_2 assump_93
        apply False.elim assump_20
      case inr assump_11 =>
        cases assump_11
        case intro assump_52 assump_53 =>
          have assump_94 : (((p4 ∧ p6) ∧ (p2 → False)) → ((p4 ∨ p3) → (p6 ∧ True))) := by
            intro assump_62
            intro assump_63
            apply And.intro
            cases assump_63
            case inl assump_64 =>
              cases assump_62
              case intro assump_68 assump_69 =>
                cases assump_68
                case intro assump_70 assump_71 =>
                  exact assump_71
            case inr assump_65 =>
              cases assump_62
              case intro assump_80 assump_81 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  exact assump_83
            apply True.intro
          let assump_61 := assump_2 assump_94
          apply False.elim assump_61


variable (p7 p5 p2 p4 p0 p1 p6 p3 : Prop)
theorem file78_45768 : (((((p6 → False) → (p7 → p7)) ∨ ((p3 ∨ p6) ∨ (p1 ∧ False))) ∨ (((p5 ∧ p4) ∧ (p3 → p0)) ∧ ((p3 → p0) ∨ (p0 → False)))) ∨ ((((p2 → p4) ∧ (p5 ∨ p6)) → False) ∧ (((p3 → True) → (True ∨ p4)) ∧ ((p1 → p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  exact assump_2


variable (p6 p5 p3 p0 p1 p2 : Prop)
theorem file78_46141 : ((((((p0 ∨ p6) → False) ∧ ((True → p6) → (p1 ∧ p2))) ∧ (((p5 → False) → False) ∨ ((False ∧ p3) → (p0 ∧ p0)))) ∧ ((((True → False) → False) → False) ∧ (((p2 ∧ False) → False) ∧ ((p1 → False) ∧ (p5 ∨ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_25
                case inl assump_28 =>
                  have assump_92 : ((True → False) → False) := by
                    intro assump_36
                    have assump_93 : True := by
                      apply True.intro
                    let assump_39 := assump_36 assump_93
                    apply False.elim assump_39
                  let assump_35 := assump_16 assump_92
                  apply False.elim assump_35
                case inr assump_29 =>
                  have assump_94 : p1 := by
                    exact assump_29
                  let assump_49 := assump_24 assump_94
                  apply False.elim assump_49
        case inr assump_13 =>
          cases assump_3
          case intro assump_55 assump_56 =>
            cases assump_56
            case intro assump_59 assump_60 =>
              cases assump_60
              case intro assump_63 assump_64 =>
                cases assump_64
                case inl assump_67 =>
                  have assump_95 : ((True → False) → False) := by
                    intro assump_75
                    have assump_96 : True := by
                      apply True.intro
                    let assump_78 := assump_75 assump_96
                    apply False.elim assump_78
                  let assump_74 := assump_55 assump_95
                  apply False.elim assump_74
                case inr assump_68 =>
                  have assump_97 : p1 := by
                    exact assump_68
                  let assump_88 := assump_63 assump_97
                  apply False.elim assump_88


variable (p5 p6 p1 p2 p4 p3 : Prop)
theorem file78_48491 : ((((((p3 ∧ False) → (p6 → p4)) → False) → (((p6 ∧ p5) → False) ∧ ((p2 ∧ p4) ∨ (False ∨ p3)))) → ((((p3 → p3) → False) → ((p1 ∨ p2) → (p6 → False))) → False)) → False) := by
  intro assump_1
  have assump_78 : ((((p3 ∧ False) → (p6 → p4)) → False) → (((p6 ∧ p5) → False) ∧ ((p2 ∧ p4) ∨ (False ∨ p3)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_79 : ((p3 ∧ False) → (p6 → p4)) := by
        intro assump_16
        intro assump_17
        cases assump_16
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
      let assump_15 := assump_5 assump_79
      apply False.elim assump_15
    have assump_80 : ((p3 ∧ False) → (p6 → p4)) := by
      intro assump_32
      intro assump_33
      cases assump_32
      case intro assump_36 assump_37 =>
        apply False.elim assump_37
    let assump_31 := assump_5 assump_80
    apply False.elim assump_31
  let assump_4 := assump_1 assump_78
  have assump_81 : (((p3 → p3) → False) → ((p1 ∨ p2) → (p6 → False))) := by
    intro assump_46
    intro assump_47
    intro assump_48
    cases assump_47
    case inl assump_51 =>
      have assump_82 : (p3 → p3) := by
        intro assump_58
        exact assump_58
      let assump_57 := assump_46 assump_82
      apply False.elim assump_57
    case inr assump_52 =>
      have assump_83 : (p3 → p3) := by
        intro assump_69
        exact assump_69
      let assump_68 := assump_46 assump_83
      apply False.elim assump_68
  let assump_45 := assump_4 assump_81
  apply False.elim assump_45


variable (p4 p2 p0 p1 p5 p3 p7 p6 : Prop)
theorem file78_50163 : ((((((p0 ∧ p1) ∨ (p2 → p2)) → ((p4 ∨ True) ∧ (True ∨ p4))) ∨ (((p3 ∧ p0) → (p6 ∨ True)) → ((False ∧ p5) ∨ (p7 → p3)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p0 ∧ p1) ∨ (p2 → p2)) → ((p4 ∨ True) ∧ (True ∨ p4))) ∨ (((p3 ∧ p0) → (p6 ∨ True)) → ((False ∧ p5) ∨ (p7 → p3)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inr
        apply True.intro
    case inr assump_7 =>
      apply Or.inr
      apply True.intro
    cases assump_5
    case inl assump_16 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        apply Or.inl
        apply True.intro
    case inr assump_17 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p5 p3 p6 p0 p4 p2 p1 : Prop)
theorem file78_51089 : (((((p3 ∨ p0) → (p6 ∧ p1)) ∧ ((p1 ∧ False) ∧ (p2 ∨ True))) → (((True → False) ∧ (p6 ∨ p2)) → ((p3 ∨ p1) → False))) ∧ ((((p1 → p1) → (p3 ∧ p3)) → ((True ∨ False) → (p4 → p4))) ∨ (((p0 ∧ p1) → (p6 → p6)) ∨ ((p7 ∧ p5) → False)))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        cases assump_1
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              apply False.elim assump_23
      case inr assump_13 =>
        cases assump_1
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_37
  case inr assump_5 =>
    cases assump_2
    case intro assump_44 assump_45 =>
      cases assump_45
      case inl assump_48 =>
        cases assump_1
        case intro assump_52 assump_53 =>
          cases assump_53
          case intro assump_56 assump_57 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              apply False.elim assump_59
      case inr assump_49 =>
        cases assump_1
        case intro assump_66 assump_67 =>
          cases assump_67
          case intro assump_70 assump_71 =>
            cases assump_70
            case intro assump_72 assump_73 =>
              apply False.elim assump_73
  apply Or.inl
  intro assump_78
  intro assump_79
  intro assump_80
  cases assump_79
  case inl assump_83 =>
    exact assump_80
  case inr assump_84 =>
    apply False.elim assump_84


variable (p2 p1 p4 p6 p0 p5 : Prop)
theorem file78_52967 : (((((p6 → False) → (True ∨ p1)) → ((False → False) → False)) ∧ (((False ∧ p5) ∧ (p0 → False)) ∧ ((p4 ∨ p1) → (p1 ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p7 p3 p2 p6 p4 : Prop)
theorem file78_53445 : ((((((True ∨ p3) → False) ∧ ((True → p6) ∧ (False ∨ p6))) → False) ∧ ((((p6 → True) → (p2 ∨ p7)) → ((False → p6) ∨ (p4 ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p6 → True) → (p2 ∨ p7)) → ((False → p6) ∨ (p4 ∨ True))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p4 p2 p1 p5 : Prop)
theorem file78_53971 : ((((((p2 → False) → (p5 → p5)) → False) → (((p4 ∧ p4) ∧ (False ∨ p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p2 → False) → (p5 → p5)) → False) → (((p4 ∧ p4) ∧ (False ∨ p1)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          apply False.elim assump_15
        case inr assump_16 =>
          have assump_37 : ((p2 → False) → (p5 → p5)) := by
            intro assump_24
            intro assump_25
            exact assump_25
          let assump_23 := assump_5 assump_37
          apply False.elim assump_23
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p2 p5 p7 p1 p6 p0 p3 : Prop)
theorem file78_54823 : (((((p7 ∨ p6) ∧ (p6 → p2)) ∨ ((p3 ∧ p1) → (True ∨ p0))) → False) → ((((p2 → False) → (p0 ∧ p1)) ∨ ((p1 ∨ True) → (p5 ∨ p7))) ∨ (((False → p3) → (p1 → False)) → ((p2 ∧ p5) ∨ (p6 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply And.intro
  have assump_33 : (((p7 ∨ p6) ∧ (p6 → p2)) ∨ ((p3 ∧ p1) → (True ∨ p0))) := by
    apply Or.inr
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply Or.inl
      apply True.intro
  let assump_8 := assump_1 assump_33
  apply False.elim assump_8
  have assump_34 : (((p7 ∨ p6) ∧ (p6 → p2)) ∨ ((p3 ∧ p1) → (True ∨ p0))) := by
    apply Or.inr
    intro assump_23
    cases assump_23
    case intro assump_24 assump_25 =>
      apply Or.inl
      apply True.intro
  let assump_22 := assump_1 assump_34
  apply False.elim assump_22


variable (p3 p6 p1 p0 : Prop)
theorem file78_55717 : ((((((False → False) ∨ (True → p1)) ∨ ((p6 ∨ p0) ∨ (p0 ∧ False))) ∨ (((p0 ∨ p3) → False) → ((False → False) → (False → p6)))) → False) → False) := by
  intro assump_20
  have assump_30 : ((((False → False) ∨ (True → p1)) ∨ ((p6 ∨ p0) ∨ (p0 ∧ False))) ∨ (((p0 ∨ p3) → False) → ((False → False) → (False → p6)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_24
    apply False.elim assump_24
  let assump_23 := assump_20 assump_30
  apply False.elim assump_23


variable (p4 p7 p3 p5 p0 p2 p6 : Prop)
theorem file78_56267 : ((((((p0 ∧ p3) → False) → False) → (((p7 ∧ p3) → (p6 ∨ p6)) → ((p2 → True) ∨ (False ∨ p2)))) ∧ ((((p0 ∨ p5) ∧ (p5 → p6)) ∧ ((True ∨ p5) ∨ (p6 → True))) ∧ (((True → False) ∧ (p2 ∧ p5)) ∧ ((p4 ∨ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_9
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_7
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    cases assump_27
                    case intro assump_30 assump_31 =>
                      have assump_168 : True := by
                        apply True.intro
                      let assump_41 := assump_26 assump_168
                      apply False.elim assump_41
              case inr assump_21 =>
                cases assump_7
                case intro assump_47 assump_48 =>
                  cases assump_47
                  case intro assump_49 assump_50 =>
                    cases assump_50
                    case intro assump_53 assump_54 =>
                      have assump_169 : True := by
                        apply True.intro
                      let assump_64 := assump_49 assump_169
                      apply False.elim assump_64
            case inr assump_19 =>
              cases assump_7
              case intro assump_70 assump_71 =>
                cases assump_70
                case intro assump_72 assump_73 =>
                  cases assump_73
                  case intro assump_76 assump_77 =>
                    have assump_170 : True := by
                      apply True.intro
                    let assump_87 := assump_72 assump_170
                    apply False.elim assump_87
          case inr assump_13 =>
            cases assump_9
            case inl assump_95 =>
              cases assump_95
              case inl assump_97 =>
                cases assump_7
                case intro assump_101 assump_102 =>
                  cases assump_101
                  case intro assump_103 assump_104 =>
                    cases assump_104
                    case intro assump_107 assump_108 =>
                      have assump_171 : True := by
                        apply True.intro
                      let assump_118 := assump_103 assump_171
                      apply False.elim assump_118
              case inr assump_98 =>
                cases assump_7
                case intro assump_124 assump_125 =>
                  cases assump_124
                  case intro assump_126 assump_127 =>
                    cases assump_127
                    case intro assump_130 assump_131 =>
                      have assump_172 : True := by
                        apply True.intro
                      let assump_141 := assump_126 assump_172
                      apply False.elim assump_141
            case inr assump_96 =>
              cases assump_7
              case intro assump_147 assump_148 =>
                cases assump_147
                case intro assump_149 assump_150 =>
                  cases assump_150
                  case intro assump_153 assump_154 =>
                    have assump_173 : True := by
                      apply True.intro
                    let assump_164 := assump_149 assump_173
                    apply False.elim assump_164


variable (p1 p2 p5 p0 p3 p4 p7 : Prop)
theorem file78_60026 : (((((p5 ∨ False) → (p1 ∨ p3)) ∨ ((False ∨ p0) → (p5 ∧ p5))) ∧ (((False → p2) ∧ (p3 → p2)) ∧ ((p7 ∧ p0) → (p4 → True)))) → ((((p7 → False) ∧ (p5 ∧ p2)) → False) → (((p1 → False) ∧ (False ∧ p4)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      apply False.elim assump_8


variable (p1 p0 p2 p4 p3 : Prop)
theorem file78_60482 : (((((p2 → False) → False) ∧ ((p2 ∨ p4) → False)) ∧ (((p1 ∨ p1) ∧ (p0 ∨ p3)) → False)) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      have assump_36 : (p2 → False) := by
        intro assump_24
        have assump_37 : (p2 ∨ p4) := by
          apply Or.inl
          exact assump_24
        let assump_29 := assump_14 assump_37
        apply False.elim assump_29
      let assump_23 := assump_13 assump_36
      apply False.elim assump_23


variable (p2 p0 p5 p4 p3 p1 p7 : Prop)
theorem file78_61088 : (((((p7 → p0) → (True → False)) ∨ ((True → False) ∨ (True ∧ p7))) → (((False → False) ∨ (p5 → True)) ∨ ((True → p4) → False))) ∨ ((((p0 → False) → (p1 → False)) ∨ ((False → False) → (p2 ∨ p3))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_9 =>
      apply Or.inl
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    case inr assump_10 =>
      cases assump_10
      case intro assump_16 assump_17 =>
        apply Or.inl
        apply Or.inl
        intro assump_22
        apply False.elim assump_22


variable (p4 p1 p6 p7 p0 p2 p5 p3 : Prop)
theorem file78_61868 : ((((((p0 ∧ p7) → False) ∧ ((p6 → False) ∨ (p0 ∨ False))) ∨ (((p7 → False) ∨ (p1 ∨ p6)) ∨ ((False ∧ p0) ∧ (p3 → False)))) ∧ ((((False → False) ∧ (p2 → False)) → ((p4 → True) → False)) ∧ (((p5 ∧ True) ∨ (p5 → True)) → False))) → False) := by
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
            have assump_93 : ((p5 ∧ True) ∨ (p5 → True)) := by
              apply Or.inr
              intro assump_21
              apply True.intro
            let assump_20 := assump_15 assump_93
            apply False.elim assump_20
        case inr assump_11 =>
          cases assump_11
          case inl assump_25 =>
            cases assump_3
            case intro assump_29 assump_30 =>
              have assump_94 : ((p5 ∧ True) ∨ (p5 → True)) := by
                apply Or.inr
                intro assump_36
                apply True.intro
              let assump_35 := assump_30 assump_94
              apply False.elim assump_35
          case inr assump_26 =>
            apply False.elim assump_26
    case inr assump_5 =>
      cases assump_5
      case inl assump_42 =>
        cases assump_42
        case inl assump_44 =>
          cases assump_3
          case intro assump_48 assump_49 =>
            have assump_95 : ((p5 ∧ True) ∨ (p5 → True)) := by
              apply Or.inr
              intro assump_55
              apply True.intro
            let assump_54 := assump_49 assump_95
            apply False.elim assump_54
        case inr assump_45 =>
          cases assump_45
          case inl assump_59 =>
            cases assump_3
            case intro assump_63 assump_64 =>
              have assump_96 : ((p5 ∧ True) ∨ (p5 → True)) := by
                apply Or.inr
                intro assump_70
                apply True.intro
              let assump_69 := assump_64 assump_96
              apply False.elim assump_69
          case inr assump_60 =>
            cases assump_3
            case intro assump_76 assump_77 =>
              have assump_97 : ((p5 ∧ True) ∨ (p5 → True)) := by
                apply Or.inr
                intro assump_83
                apply True.intro
              let assump_82 := assump_77 assump_97
              apply False.elim assump_82
      case inr assump_43 =>
        cases assump_43
        case intro assump_87 assump_88 =>
          cases assump_87
          case intro assump_89 assump_90 =>
            apply False.elim assump_89


variable (p6 p2 p3 p7 p5 p4 p1 : Prop)
theorem file78_64593 : (((((True → False) ∧ (False → False)) ∨ ((p7 → p5) → (p6 ∧ p6))) → (((False → False) ∧ (p4 ∨ p2)) ∨ ((p6 → False) ∧ (p3 ∧ p3)))) → ((((False → True) → False) → ((p3 → p7) ∨ (p2 ∧ p5))) ∨ (((p1 → False) → (p1 ∨ p6)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  have assump_16 : (False → True) := by
    intro assump_12
    apply True.intro
  let assump_11 := assump_4 assump_16
  apply False.elim assump_11


variable (p5 p0 p4 p3 p6 p1 p7 : Prop)
theorem file78_65117 : (((((p7 → p5) ∧ (p7 ∧ p6)) → False) → (((True ∨ p1) → False) ∧ ((p0 ∧ p0) ∨ (p3 → False)))) → ((((p3 ∧ p0) ∧ (p5 → False)) → ((p6 → False) → (True ∨ p4))) ∨ (((p5 ∨ p4) ∧ (p6 ∧ p3)) ∧ ((p5 ∨ p4) → (True ∨ p7))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      apply Or.inl
      apply True.intro


variable (p7 p6 p3 p4 p1 p0 p2 p5 : Prop)
theorem file78_65618 : (((((p3 ∧ False) ∧ (p7 ∨ p6)) → ((p0 → False) → False)) ∨ (((p5 ∨ p2) ∨ (True → False)) ∨ ((p0 ∧ p3) ∨ (p4 ∧ p4)))) ∨ ((((True ∧ False) ∧ (p1 → p7)) → False) ∨ (((p7 ∧ True) ∨ (p6 → p5)) ∨ ((p1 ∧ p2) → (p0 ∧ p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p4 p1 p7 p3 p2 p0 : Prop)
theorem file78_66102 : ((((((True ∨ True) ∧ (p4 → False)) ∨ ((p1 ∧ p1) → False)) → (((p1 → False) → False) ∨ ((p2 → False) ∨ (p0 ∧ False)))) ∧ ((((p3 ∨ p0) → (p0 ∧ p7)) → ((p1 ∧ False) → False)) ∧ (((False ∨ p2) ∧ (p1 ∧ False)) ∧ ((p7 → p7) ∧ (False ∧ False))))) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_21
          case inl assump_23 =>
            apply False.elim assump_23
          case inr assump_24 =>
            cases assump_22
            case intro assump_29 assump_30 =>
              apply False.elim assump_30


variable (p6 p2 p7 p4 p5 p3 p0 : Prop)
theorem file78_66922 : (((((False → False) → (p2 ∧ p7)) ∧ ((p5 → False) → False)) ∨ (((p3 → p3) → False) ∧ ((False → False) ∨ (p0 → False)))) → ((((p5 ∨ True) → (p4 ∨ True)) → ((p2 → False) → (p7 → True))) ∨ (((p4 ∨ p6) → (p0 ∨ p4)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      intro assump_12
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_13 assump_14 =>
      cases assump_14
      case inl assump_17 =>
        apply Or.inl
        intro assump_21
        intro assump_22
        intro assump_23
        apply True.intro
      case inr assump_18 =>
        apply Or.inl
        intro assump_26
        intro assump_27
        intro assump_28
        apply True.intro


variable (p4 p3 p7 p5 p1 p2 : Prop)
theorem file78_67823 : (((((p5 → p3) → False) ∨ ((p2 ∧ p5) ∧ (p3 → False))) ∧ (((p1 → False) → (p1 → False)) → False)) → ((((p7 → False) → (p4 ∨ False)) → False) ∧ (((p7 → False) → (p2 ∨ p4)) → ((p3 ∨ False) ∧ (False → True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_105 : ((p1 → False) → (p1 → False)) := by
        intro assump_14
        intro assump_15
        have assump_106 : p1 := by
          exact assump_15
        let assump_20 := assump_14 assump_106
        apply False.elim assump_20
      let assump_13 := assump_6 assump_105
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          have assump_107 : ((p1 → False) → (p1 → False)) := by
            intro assump_40
            intro assump_41
            have assump_108 : p1 := by
              exact assump_41
            let assump_46 := assump_40 assump_108
            apply False.elim assump_46
          let assump_39 := assump_6 assump_107
          apply False.elim assump_39
  intro assump_53
  apply And.intro
  cases assump_1
  case intro assump_56 assump_57 =>
    cases assump_56
    case inl assump_58 =>
      have assump_109 : ((p1 → False) → (p1 → False)) := by
        intro assump_65
        intro assump_66
        have assump_110 : p1 := by
          exact assump_66
        let assump_71 := assump_65 assump_110
        apply False.elim assump_71
      let assump_64 := assump_57 assump_109
      apply False.elim assump_64
    case inr assump_59 =>
      cases assump_59
      case intro assump_78 assump_79 =>
        cases assump_78
        case intro assump_80 assump_81 =>
          have assump_111 : ((p1 → False) → (p1 → False)) := by
            intro assump_91
            intro assump_92
            have assump_112 : p1 := by
              exact assump_92
            let assump_97 := assump_91 assump_112
            apply False.elim assump_97
          let assump_90 := assump_57 assump_111
          apply False.elim assump_90
  intro assump_104
  apply True.intro


variable (p0 p5 p3 p1 p7 p4 p6 p2 : Prop)
theorem file78_70105 : ((((((True → False) ∨ (p4 ∧ False)) → ((p5 → p7) ∧ (p6 ∧ p0))) → False) ∧ ((((True → False) → (p2 ∧ p3)) → ((p1 → p0) ∧ (p4 → p1))) ∨ (((p0 ∧ p5) → (p7 → p7)) ∨ ((p7 ∨ True) ∨ (p3 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_345 : (((True → False) ∨ (p4 ∧ False)) → ((p5 → p7) ∧ (p6 ∧ p0))) := by
        intro assump_28
        apply And.intro
        intro assump_29
        cases assump_28
        case inl assump_32 =>
          have assump_346 : True := by
            apply True.intro
          let assump_36 := assump_32 assump_346
          apply False.elim assump_36
        case inr assump_33 =>
          cases assump_33
          case intro assump_40 assump_41 =>
            apply False.elim assump_41
        apply And.intro
        cases assump_28
        case inl assump_46 =>
          have assump_347 : True := by
            apply True.intro
          let assump_50 := assump_46 assump_347
          apply False.elim assump_50
        case inr assump_47 =>
          cases assump_47
          case intro assump_54 assump_55 =>
            apply False.elim assump_55
        cases assump_28
        case inl assump_60 =>
          have assump_348 : True := by
            apply True.intro
          let assump_64 := assump_60 assump_348
          apply False.elim assump_64
        case inr assump_61 =>
          cases assump_61
          case intro assump_68 assump_69 =>
            apply False.elim assump_69
      let assump_27 := assump_2 assump_345
      apply False.elim assump_27
    case inr assump_7 =>
      cases assump_7
      case inl assump_77 =>
        have assump_349 : (((True → False) ∨ (p4 ∧ False)) → ((p5 → p7) ∧ (p6 ∧ p0))) := by
          intro assump_83
          apply And.intro
          intro assump_84
          cases assump_83
          case inl assump_87 =>
            have assump_350 : True := by
              apply True.intro
            let assump_91 := assump_87 assump_350
            apply False.elim assump_91
          case inr assump_88 =>
            cases assump_88
            case intro assump_95 assump_96 =>
              apply False.elim assump_96
          apply And.intro
          cases assump_83
          case inl assump_101 =>
            have assump_351 : True := by
              apply True.intro
            let assump_105 := assump_101 assump_351
            apply False.elim assump_105
          case inr assump_102 =>
            cases assump_102
            case intro assump_109 assump_110 =>
              apply False.elim assump_110
          cases assump_83
          case inl assump_115 =>
            have assump_352 : True := by
              apply True.intro
            let assump_119 := assump_115 assump_352
            apply False.elim assump_119
          case inr assump_116 =>
            cases assump_116
            case intro assump_123 assump_124 =>
              apply False.elim assump_124
        let assump_82 := assump_2 assump_349
        apply False.elim assump_82
      case inr assump_78 =>
        cases assump_78
        case inl assump_132 =>
          cases assump_132
          case inl assump_134 =>
            have assump_353 : (((True → False) ∨ (p4 ∧ False)) → ((p5 → p7) ∧ (p6 ∧ p0))) := by
              intro assump_140
              apply And.intro
              intro assump_141
              cases assump_140
              case inl assump_144 =>
                exact assump_134
              case inr assump_145 =>
                cases assump_145
                case intro assump_148 assump_149 =>
                  apply False.elim assump_149
              apply And.intro
              cases assump_140
              case inl assump_154 =>
                have assump_354 : True := by
                  apply True.intro
                let assump_158 := assump_154 assump_354
                apply False.elim assump_158
              case inr assump_155 =>
                cases assump_155
                case intro assump_162 assump_163 =>
                  apply False.elim assump_163
              cases assump_140
              case inl assump_168 =>
                have assump_355 : True := by
                  apply True.intro
                let assump_172 := assump_168 assump_355
                apply False.elim assump_172
              case inr assump_169 =>
                cases assump_169
                case intro assump_176 assump_177 =>
                  apply False.elim assump_177
            let assump_139 := assump_2 assump_353
            apply False.elim assump_139
          case inr assump_135 =>
            have assump_356 : (((True → False) ∨ (p4 ∧ False)) → ((p5 → p7) ∧ (p6 ∧ p0))) := by
              intro assump_188
              apply And.intro
              intro assump_189
              cases assump_188
              case inl assump_192 =>
                have assump_357 : True := by
                  apply True.intro
                let assump_196 := assump_192 assump_357
                apply False.elim assump_196
              case inr assump_193 =>
                cases assump_193
                case intro assump_200 assump_201 =>
                  apply False.elim assump_201
              apply And.intro
              cases assump_188
              case inl assump_206 =>
                have assump_358 : True := by
                  apply True.intro
                let assump_210 := assump_206 assump_358
                apply False.elim assump_210
              case inr assump_207 =>
                cases assump_207
                case intro assump_214 assump_215 =>
                  apply False.elim assump_215
              cases assump_188
              case inl assump_220 =>
                have assump_359 : True := by
                  apply True.intro
                let assump_224 := assump_220 assump_359
                apply False.elim assump_224
              case inr assump_221 =>
                cases assump_221
                case intro assump_228 assump_229 =>
                  apply False.elim assump_229
            let assump_187 := assump_2 assump_356
            apply False.elim assump_187
        case inr assump_133 =>
          cases assump_133
          case inl assump_237 =>
            have assump_360 : (((True → False) ∨ (p4 ∧ False)) → ((p5 → p7) ∧ (p6 ∧ p0))) := by
              intro assump_243
              apply And.intro
              intro assump_244
              cases assump_243
              case inl assump_247 =>
                have assump_361 : True := by
                  apply True.intro
                let assump_251 := assump_247 assump_361
                apply False.elim assump_251
              case inr assump_248 =>
                cases assump_248
                case intro assump_255 assump_256 =>
                  apply False.elim assump_256
              apply And.intro
              cases assump_243
              case inl assump_261 =>
                have assump_362 : True := by
                  apply True.intro
                let assump_265 := assump_261 assump_362
                apply False.elim assump_265
              case inr assump_262 =>
                cases assump_262
                case intro assump_269 assump_270 =>
                  apply False.elim assump_270
              cases assump_243
              case inl assump_275 =>
                have assump_363 : True := by
                  apply True.intro
                let assump_279 := assump_275 assump_363
                apply False.elim assump_279
              case inr assump_276 =>
                cases assump_276
                case intro assump_283 assump_284 =>
                  apply False.elim assump_284
            let assump_242 := assump_2 assump_360
            apply False.elim assump_242
          case inr assump_238 =>
            have assump_364 : (((True → False) ∨ (p4 ∧ False)) → ((p5 → p7) ∧ (p6 ∧ p0))) := by
              intro assump_296
              apply And.intro
              intro assump_297
              cases assump_296
              case inl assump_300 =>
                have assump_365 : True := by
                  apply True.intro
                let assump_304 := assump_300 assump_365
                apply False.elim assump_304
              case inr assump_301 =>
                cases assump_301
                case intro assump_308 assump_309 =>
                  apply False.elim assump_309
              apply And.intro
              cases assump_296
              case inl assump_314 =>
                have assump_366 : True := by
                  apply True.intro
                let assump_318 := assump_314 assump_366
                apply False.elim assump_318
              case inr assump_315 =>
                cases assump_315
                case intro assump_322 assump_323 =>
                  apply False.elim assump_323
              cases assump_296
              case inl assump_328 =>
                have assump_367 : True := by
                  apply True.intro
                let assump_332 := assump_328 assump_367
                apply False.elim assump_332
              case inr assump_329 =>
                cases assump_329
                case intro assump_336 assump_337 =>
                  apply False.elim assump_337
            let assump_295 := assump_2 assump_364
            apply False.elim assump_295


variable (p0 p5 p7 : Prop)
theorem file78_79616 : (((((p5 → False) ∨ (True → False)) → False) ∧ (((p7 → p0) ∨ (p0 ∨ p0)) ∧ ((p0 ∧ False) ∧ (p5 → False)))) → False) := by
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


variable (p1 p0 p5 p3 p4 p2 : Prop)
theorem file78_80619 : (((((False ∨ p5) → False) → False) → False) → ((((p1 → p1) → False) → False) ∨ (((p5 → p0) ∧ (p2 → True)) ∨ ((p3 ∧ p4) ∨ (p5 → p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (p1 → p1) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p1 p3 p6 p7 p2 : Prop)
theorem file78_81004 : (((((p2 ∨ p7) ∨ (p2 ∧ p3)) ∨ ((p1 → False) → (False → p6))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p2 ∨ p7) ∨ (p2 ∧ p3)) ∨ ((p1 → False) → (False → p6))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p2 p1 p7 : Prop)
theorem file78_81392 : (((((True ∧ False) ∧ (p2 ∨ p7)) ∧ ((p7 ∧ p7) ∨ (p1 → p1))) → False) ∨ ((((p0 ∨ True) ∨ (False ∧ p7)) → False) → False)) := by
  apply Or.inl
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_20


variable (p6 p5 p3 p2 : Prop)
theorem file78_81814 : ((((((p2 → True) ∧ (p5 → False)) → False) → False) ∧ ((((True → False) ∧ (p3 → p6)) → False) → False)) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    have assump_36 : (((True → False) ∧ (p3 → p6)) → False) := by
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        have assump_37 : True := by
          apply True.intro
        let assump_29 := assump_22 assump_37
        apply False.elim assump_29
    let assump_20 := assump_15 assump_36
    apply False.elim assump_20


variable (p3 p5 p6 p2 p1 p4 : Prop)
theorem file78_82429 : (((((False ∨ True) ∨ (p1 → False)) ∨ ((p2 ∧ p3) → (p6 ∨ p5))) → False) → ((((False ∨ True) → (p2 → True)) ∨ ((True ∧ p5) → (p3 → p4))) → (((False → p6) → False) → False))) := by
  intro assump_23
  intro assump_24
  intro assump_25
  cases assump_24
  case inl assump_28 =>
    have assump_46 : (((False ∨ True) ∨ (p1 → False)) ∨ ((p2 ∧ p3) → (p6 ∨ p5))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_34 := assump_23 assump_46
    apply False.elim assump_34
  case inr assump_29 =>
    have assump_47 : (((False ∨ True) ∨ (p1 → False)) ∨ ((p2 ∧ p3) → (p6 ∨ p5))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_42 := assump_23 assump_47
    apply False.elim assump_42


variable (p2 p6 p5 p4 p7 p3 p1 : Prop)
theorem file78_83268 : ((((((p4 → p7) ∧ (p2 ∧ p5)) → ((False ∨ p3) → (False → False))) ∧ (((p6 ∧ False) ∧ (True → False)) ∨ ((p5 ∧ p5) → (False → p3)))) ∧ ((((p2 → p7) ∨ (p4 → False)) ∧ ((p1 → False) → False)) ∧ (((True ∨ p6) → False) ∧ ((p5 → False) ∧ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13
      case inr assump_9 =>
        cases assump_3
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            cases assump_22
            case inl assump_24 =>
              cases assump_21
              case intro assump_30 assump_31 =>
                cases assump_31
                case intro assump_34 assump_35 =>
                  have assump_66 : (True ∨ p6) := by
                    apply Or.inl
                    apply True.intro
                  let assump_42 := assump_30 assump_66
                  apply False.elim assump_42
            case inr assump_25 =>
              cases assump_21
              case intro assump_50 assump_51 =>
                cases assump_51
                case intro assump_54 assump_55 =>
                  have assump_67 : (True ∨ p6) := by
                    apply Or.inl
                    apply True.intro
                  let assump_62 := assump_50 assump_67
                  apply False.elim assump_62


variable (p4 p6 p3 p5 p1 : Prop)
theorem file78_84959 : ((((((False → p1) ∧ (p3 ∧ p1)) → False) → (((p6 → False) → (p5 → True)) ∨ ((p3 → False) ∨ (p4 ∧ False)))) → False) → False) := by
  intro assump_25
  have assump_37 : ((((False → p1) ∧ (p3 ∧ p1)) → False) → (((p6 → False) → (p5 → True)) ∨ ((p3 → False) ∨ (p4 ∧ False)))) := by
    intro assump_29
    apply Or.inl
    intro assump_32
    intro assump_33
    apply True.intro
  let assump_28 := assump_25 assump_37
  apply False.elim assump_28


variable (p1 p4 p5 p7 p2 p3 : Prop)
theorem file78_85462 : (((((p1 → False) → False) ∧ ((p2 ∨ p7) ∨ (False ∧ p1))) ∧ (((p5 → False) ∧ (p5 ∧ True)) ∨ ((p2 ∨ p1) ∧ (p3 ∧ p2)))) → ((((True → False) → False) ∧ ((True ∨ False) ∨ (p3 → False))) ∨ (((p2 ∨ p4) → (p7 ∧ True)) ∨ ((p2 ∨ p7) → False)))) := by
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
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                apply Or.inl
                apply And.intro
                intro assump_26
                have assump_126 : True := by
                  apply True.intro
                let assump_29 := assump_26 assump_126
                apply False.elim assump_29
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_15 =>
            cases assump_15
            case intro assump_33 assump_34 =>
              cases assump_33
              case inl assump_35 =>
                cases assump_34
                case intro assump_39 assump_40 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_45
                  have assump_127 : True := by
                    apply True.intro
                  let assump_48 := assump_45 assump_127
                  apply False.elim assump_48
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
              case inr assump_36 =>
                cases assump_34
                case intro assump_54 assump_55 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_60
                  have assump_128 : True := by
                    apply True.intro
                  let assump_63 := assump_60 assump_128
                  apply False.elim assump_63
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
        case inr assump_11 =>
          cases assump_3
          case inl assump_69 =>
            cases assump_69
            case intro assump_71 assump_72 =>
              cases assump_72
              case intro assump_75 assump_76 =>
                apply Or.inl
                apply And.intro
                intro assump_81
                have assump_129 : True := by
                  apply True.intro
                let assump_84 := assump_81 assump_129
                apply False.elim assump_84
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_70 =>
            cases assump_70
            case intro assump_88 assump_89 =>
              cases assump_88
              case inl assump_90 =>
                cases assump_89
                case intro assump_94 assump_95 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_100
                  have assump_130 : True := by
                    apply True.intro
                  let assump_103 := assump_100 assump_130
                  apply False.elim assump_103
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
              case inr assump_91 =>
                cases assump_89
                case intro assump_109 assump_110 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_115
                  have assump_131 : True := by
                    apply True.intro
                  let assump_118 := assump_115 assump_131
                  apply False.elim assump_118
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
      case inr assump_9 =>
        cases assump_9
        case intro assump_122 assump_123 =>
          apply False.elim assump_122


variable (p4 p3 p0 : Prop)
theorem file78_89557 : (((((p4 ∧ False) → False) ∨ ((p3 ∨ True) → (p0 ∧ p0))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p4 ∧ False) → False) ∨ ((p3 ∨ True) → (p0 ∧ p0))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p2 p3 p5 p6 p7 p1 p4 : Prop)
theorem file78_89985 : (((((p4 → p1) ∨ (p1 ∧ p6)) → False) → False) → ((((p3 ∧ p0) ∧ (p7 ∨ p3)) ∨ ((p1 ∧ False) → (p1 → False))) ∨ (((p0 → False) → (p0 ∧ True)) ∨ ((p0 ∨ True) ∧ (p5 → p2))))) := by
  intro assump_6
  apply Or.inl
  apply Or.inr
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    apply False.elim assump_14


variable (p5 p1 p0 : Prop)
theorem file78_90377 : ((((((p5 → False) ∨ (p5 ∨ p1)) → False) → (((False ∧ p0) → False) ∨ ((p5 → True) → False))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p5 → False) ∨ (p5 ∨ p1)) → False) → (((False ∧ p0) → False) ∨ ((p5 → True) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p5 p6 : Prop)
theorem file78_90884 : ((((((p5 ∧ False) → (p6 → p4)) → False) → False) → False) → False) := by
  intro assump_22
  have assump_46 : ((((p5 ∧ False) → (p6 → p4)) → False) → False) := by
    intro assump_26
    have assump_47 : ((p5 ∧ False) → (p6 → p4)) := by
      intro assump_30
      intro assump_31
      cases assump_30
      case intro assump_34 assump_35 =>
        apply False.elim assump_35
    let assump_29 := assump_26 assump_47
    apply False.elim assump_29
  let assump_25 := assump_22 assump_46
  apply False.elim assump_25


variable (p5 p4 p2 p0 p7 p3 p6 : Prop)
theorem file78_91465 : ((((((p2 → p5) → False) ∧ ((True ∧ p6) ∨ (p4 ∨ p5))) ∧ (((p7 ∧ False) → (p4 ∧ p2)) → False)) ∧ ((((p7 ∧ p0) ∧ (False ∨ p2)) → False) ∧ (((p3 → False) ∧ (p3 ∧ p0)) ∧ ((p7 ∨ False) ∧ (p0 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_27
                  case intro assump_30 assump_31 =>
                    cases assump_25
                    case intro assump_36 assump_37 =>
                      cases assump_36
                      case inl assump_38 =>
                        cases assump_37
                        case intro assump_42 assump_43 =>
                          have assump_147 : p3 := by
                            exact assump_30
                          let assump_53 := assump_26 assump_147
                          apply False.elim assump_53
                      case inr assump_39 =>
                        apply False.elim assump_39
        case inr assump_11 =>
          cases assump_11
          case inl assump_59 =>
            cases assump_3
            case intro assump_65 assump_66 =>
              cases assump_66
              case intro assump_69 assump_70 =>
                cases assump_69
                case intro assump_71 assump_72 =>
                  cases assump_72
                  case intro assump_75 assump_76 =>
                    cases assump_70
                    case intro assump_81 assump_82 =>
                      cases assump_81
                      case inl assump_83 =>
                        cases assump_82
                        case intro assump_87 assump_88 =>
                          have assump_148 : p3 := by
                            exact assump_75
                          let assump_98 := assump_71 assump_148
                          apply False.elim assump_98
                      case inr assump_84 =>
                        apply False.elim assump_84
          case inr assump_60 =>
            cases assump_3
            case intro assump_108 assump_109 =>
              cases assump_109
              case intro assump_112 assump_113 =>
                cases assump_112
                case intro assump_114 assump_115 =>
                  cases assump_115
                  case intro assump_118 assump_119 =>
                    cases assump_113
                    case intro assump_124 assump_125 =>
                      cases assump_124
                      case inl assump_126 =>
                        cases assump_125
                        case intro assump_130 assump_131 =>
                          have assump_149 : p3 := by
                            exact assump_118
                          let assump_141 := assump_114 assump_149
                          apply False.elim assump_141
                      case inr assump_127 =>
                        apply False.elim assump_127


variable (p5 p1 p3 p2 p6 p4 p7 : Prop)
theorem file78_94882 : (((((p4 → p1) → False) → ((p3 ∨ p1) → False)) ∨ (((p5 → False) → False) ∨ ((p6 → False) ∧ (p5 ∨ p3)))) → ((((p3 ∧ p7) → (p3 ∨ True)) ∨ ((p6 ∨ p7) ∧ (p2 → p3))) ∨ (((p6 → False) → False) → ((p3 ∨ p6) ∧ (p2 ∨ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inl
      exact assump_7
  case inr assump_3 =>
    cases assump_3
    case inl assump_13 =>
      apply Or.inl
      apply Or.inl
      intro assump_17
      cases assump_17
      case intro assump_18 assump_19 =>
        apply Or.inl
        exact assump_18
    case inr assump_14 =>
      cases assump_14
      case intro assump_24 assump_25 =>
        cases assump_25
        case inl assump_28 =>
          apply Or.inl
          apply Or.inl
          intro assump_32
          cases assump_32
          case intro assump_33 assump_34 =>
            apply Or.inl
            exact assump_33
        case inr assump_29 =>
          apply Or.inl
          apply Or.inl
          intro assump_41
          cases assump_41
          case intro assump_42 assump_43 =>
            apply Or.inl
            exact assump_42


variable (p1 p6 p5 p3 p2 p4 p0 p7 : Prop)
theorem file78_96174 : ((((((p7 → p0) ∧ (True → False)) → ((p1 → p3) → (p3 ∧ p6))) → (((p4 ∨ p6) ∨ (True → False)) ∨ ((p0 ∨ True) ∧ (p4 ∨ p2)))) ∧ ((((p5 ∨ p1) → (p0 → False)) → False) ∧ (((p0 → False) ∧ (p5 ∧ p3)) ∧ ((p4 ∨ p7) ∨ (p1 → p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_11
            case inl assump_22 =>
              cases assump_22
              case inl assump_24 =>
                have assump_141 : ((p5 ∨ p1) → (p0 → False)) := by
                  intro assump_33
                  intro assump_34
                  cases assump_33
                  case inl assump_37 =>
                    have assump_142 : p0 := by
                      exact assump_34
                    let assump_46 := assump_12 assump_142
                    apply False.elim assump_46
                  case inr assump_38 =>
                    have assump_143 : p0 := by
                      exact assump_34
                    let assump_57 := assump_12 assump_143
                    apply False.elim assump_57
                let assump_32 := assump_6 assump_141
                apply False.elim assump_32
              case inr assump_25 =>
                have assump_144 : ((p5 ∨ p1) → (p0 → False)) := by
                  intro assump_71
                  intro assump_72
                  cases assump_71
                  case inl assump_75 =>
                    have assump_145 : p0 := by
                      exact assump_72
                    let assump_84 := assump_12 assump_145
                    apply False.elim assump_84
                  case inr assump_76 =>
                    have assump_146 : p0 := by
                      exact assump_72
                    let assump_95 := assump_12 assump_146
                    apply False.elim assump_95
                let assump_70 := assump_6 assump_144
                apply False.elim assump_70
            case inr assump_23 =>
              have assump_147 : ((p5 ∨ p1) → (p0 → False)) := by
                intro assump_109
                intro assump_110
                cases assump_109
                case inl assump_113 =>
                  have assump_148 : p0 := by
                    exact assump_110
                  let assump_122 := assump_12 assump_148
                  apply False.elim assump_122
                case inr assump_114 =>
                  have assump_149 : p0 := by
                    exact assump_110
                  let assump_134 := assump_12 assump_149
                  apply False.elim assump_134
              let assump_108 := assump_6 assump_147
              apply False.elim assump_108


variable (p5 p4 p1 p6 p0 p3 : Prop)
theorem file78_99144 : (((((p6 ∨ p6) ∨ (p5 → False)) → False) → (((p1 ∧ p6) ∧ (True → p3)) ∨ ((False ∧ p6) → (p1 → p0)))) ∨ ((((p5 ∧ p4) → (p6 ∧ p4)) ∧ ((p5 ∧ p3) → False)) ∧ (((p5 ∨ p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p2 p7 p0 p4 p6 : Prop)
theorem file78_99553 : (((((p2 → False) ∨ (False → False)) → False) ∧ (((True → False) → False) ∧ ((p0 ∨ p4) → False))) → ((((p4 ∧ p4) → (True ∨ p4)) ∨ ((p7 → False) → False)) ∨ (((p4 ∨ True) → False) ∨ ((p6 ∧ True) ∧ (p0 ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply Or.inl
        apply True.intro


variable (p6 p4 p7 p3 p5 p0 p1 : Prop)
theorem file78_100122 : (((((p6 ∧ p7) ∧ (True ∧ False)) ∧ ((p1 → p1) ∧ (p7 ∧ p4))) → False) → ((((p3 ∧ True) → False) ∧ ((p3 → False) ∧ (True ∧ p3))) → (((True ∧ p7) ∨ (p6 ∨ p6)) → ((p0 ∨ p3) ∧ (p5 ∨ False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            apply Or.inr
            exact assump_21
  case inr assump_5 =>
    cases assump_5
    case inl assump_28 =>
      cases assump_2
      case intro assump_32 assump_33 =>
        cases assump_33
        case intro assump_36 assump_37 =>
          cases assump_37
          case intro assump_40 assump_41 =>
            apply Or.inr
            exact assump_41
    case inr assump_29 =>
      cases assump_2
      case intro assump_50 assump_51 =>
        cases assump_51
        case intro assump_54 assump_55 =>
          cases assump_55
          case intro assump_58 assump_59 =>
            apply Or.inr
            exact assump_59
  cases assump_3
  case inl assump_66 =>
    cases assump_66
    case intro assump_68 assump_69 =>
      cases assump_2
      case intro assump_74 assump_75 =>
        cases assump_75
        case intro assump_78 assump_79 =>
          cases assump_79
          case intro assump_82 assump_83 =>
            have assump_146 : p3 := by
              exact assump_83
            let assump_92 := assump_78 assump_146
            apply False.elim assump_92
  case inr assump_67 =>
    cases assump_67
    case inl assump_96 =>
      cases assump_2
      case intro assump_100 assump_101 =>
        cases assump_101
        case intro assump_104 assump_105 =>
          cases assump_105
          case intro assump_108 assump_109 =>
            have assump_147 : p3 := by
              exact assump_109
            let assump_118 := assump_104 assump_147
            apply False.elim assump_118
    case inr assump_97 =>
      cases assump_2
      case intro assump_124 assump_125 =>
        cases assump_125
        case intro assump_128 assump_129 =>
          cases assump_129
          case intro assump_132 assump_133 =>
            have assump_148 : p3 := by
              exact assump_133
            let assump_142 := assump_128 assump_148
            apply False.elim assump_142


variable (p1 p4 p6 p5 p0 p3 p2 : Prop)
theorem file78_102670 : (((((False → False) → (p1 ∧ p1)) ∧ ((p0 ∧ p1) → (p2 ∨ p1))) → (((p5 → p5) → False) → ((p0 → True) ∧ (p6 ∨ p2)))) ∨ ((((p4 → False) → False) ∧ ((p5 → False) ∨ (p0 → p2))) ∧ (((p5 → p0) → False) ∧ ((p1 ∧ True) → (p6 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply True.intro
  cases assump_1
  case intro assump_6 assump_7 =>
    have assump_27 : (p5 → p5) := by
      intro assump_21
      exact assump_21
    let assump_20 := assump_2 assump_27
    apply False.elim assump_20


variable (p6 p4 p2 p3 : Prop)
theorem file78_103260 : ((((((p4 → False) → (p6 → p4)) → ((p4 → False) → False)) → False) ∧ ((((p6 ∨ p3) ∧ (p2 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_33 : (((p6 ∨ p3) ∧ (p2 ∧ False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
        case inr assump_13 =>
          cases assump_11
          case intro assump_24 assump_25 =>
            apply False.elim assump_25
    let assump_8 := assump_3 assump_33
    apply False.elim assump_8


variable (p6 p2 p5 : Prop)
theorem file78_104027 : ((((((False → False) ∧ (True → False)) → False) ∨ (((True → False) ∧ (p6 ∧ p2)) ∧ ((p5 ∧ p2) ∨ (False ∨ p2)))) → False) → False) := by
  intro assump_7
  have assump_25 : ((((False → False) ∧ (True → False)) → False) ∨ (((True → False) ∧ (p6 ∧ p2)) ∧ ((p5 ∧ p2) ∨ (False ∨ p2)))) := by
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      have assump_26 : True := by
        apply True.intro
      let assump_18 := assump_13 assump_26
      apply False.elim assump_18
  let assump_10 := assump_7 assump_25
  apply False.elim assump_10


variable (p2 p6 p5 p3 p7 p0 p1 : Prop)
theorem file78_104673 : (((((True → False) ∧ (p7 ∨ p7)) → False) ∨ (((True ∨ True) → (p3 ∨ p6)) → ((p5 ∧ p2) ∧ (p2 ∧ p0)))) ∨ ((((p5 ∧ p2) → False) → ((p0 → p1) → False)) ∧ (((True ∧ False) → False) ∨ ((p3 ∨ p3) → (p7 → p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_22 : True := by
        apply True.intro
      let assump_11 := assump_2 assump_22
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_23 : True := by
        apply True.intro
      let assump_18 := assump_2 assump_23
      apply False.elim assump_18


variable (p0 p7 p4 p6 p3 p5 p1 : Prop)
theorem file78_105381 : (((((p5 ∨ p0) → (p4 → p1)) → ((False → p4) ∨ (True ∨ p4))) ∨ (((p5 → False) → False) → ((p5 ∧ p1) → (p7 ∨ p3)))) ∨ ((((False ∧ p6) → (p0 ∧ p6)) → ((p4 ∨ False) → False)) → (((p5 → p0) → (p6 ∨ p6)) ∧ ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p7 p3 p5 : Prop)
theorem file78_105770 : (((((False → p5) ∧ (p7 → False)) → ((False ∧ p3) → (p7 → p7))) → False) → False) := by
  intro assump_9
  have assump_25 : (((False → p5) ∧ (p7 → False)) → ((False ∧ p3) → (p7 → p7))) := by
    intro assump_13
    intro assump_14
    intro assump_15
    cases assump_14
    case intro assump_18 assump_19 =>
      apply False.elim assump_18
  let assump_12 := assump_9 assump_25
  apply False.elim assump_12


variable (p1 p0 p6 p2 p7 p4 p5 p3 : Prop)
theorem file78_106244 : (((((False ∧ p2) → False) → False) ∧ (((p1 ∧ p5) → False) ∧ ((p5 → p4) ∨ (False → p2)))) → ((((p4 ∧ p0) ∧ (p0 → p3)) → False) → (((p6 → False) → (p7 ∨ p3)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        have assump_44 : ((False ∧ p2) → False) := by
          intro assump_23
          cases assump_23
          case intro assump_24 assump_25 =>
            apply False.elim assump_24
        let assump_22 := assump_8 assump_44
        apply False.elim assump_22
      case inr assump_17 =>
        have assump_45 : ((False ∧ p2) → False) := by
          intro assump_36
          cases assump_36
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
        let assump_35 := assump_8 assump_45
        apply False.elim assump_35


variable (p1 p5 p3 p0 p2 : Prop)
theorem file78_107247 : ((((((p1 ∧ True) ∧ (False → p1)) → ((p0 → False) → (p0 → p2))) ∧ (((True → False) ∧ (p5 ∨ p1)) → ((p0 → p3) ∨ (p5 ∨ True)))) → False) → False) := by
  intro assump_4
  have assump_63 : ((((p1 ∧ True) ∧ (False → p1)) → ((p0 → False) → (p0 → p2))) ∧ (((True → False) ∧ (p5 ∨ p1)) → ((p0 → p3) ∨ (p5 ∨ True)))) := by
    apply And.intro
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_8
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        have assump_64 : p0 := by
          exact assump_10
        let assump_27 := assump_9 assump_64
        apply False.elim assump_27
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      cases assump_33
      case inl assump_36 =>
        apply Or.inl
        intro assump_40
        have assump_65 : True := by
          apply True.intro
        let assump_45 := assump_32 assump_65
        apply False.elim assump_45
      case inr assump_37 =>
        apply Or.inl
        intro assump_51
        have assump_66 : True := by
          apply True.intro
        let assump_56 := assump_32 assump_66
        apply False.elim assump_56
  let assump_7 := assump_4 assump_63
  apply False.elim assump_7


variable (p3 p0 p2 p6 p5 p1 : Prop)
theorem file78_108554 : ((((((p0 ∨ True) → (p1 → False)) ∧ ((p6 → True) → False)) → (((p5 ∧ True) → False) ∨ ((p1 → False) ∨ (p2 ∧ p3)))) → False) → False) := by
  intro assump_12
  have assump_39 : ((((p0 ∨ True) → (p1 → False)) ∧ ((p6 → True) → False)) → (((p5 ∧ True) → False) ∨ ((p1 → False) ∨ (p2 ∧ p3)))) := by
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply Or.inl
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        have assump_40 : (p6 → True) := by
          intro assump_32
          apply True.intro
        let assump_31 := assump_18 assump_40
        apply False.elim assump_31
  let assump_15 := assump_12 assump_39
  apply False.elim assump_15


variable (p6 p5 p0 p2 p7 : Prop)
theorem file78_109329 : ((((((p0 ∧ True) → False) ∨ ((p7 → False) ∨ (p2 ∧ p5))) → (((p0 → p6) ∧ (p5 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p0 ∧ True) → False) ∨ ((p7 → False) ∨ (p2 ∧ p5))) → (((p0 → p6) ∧ (p5 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p4 p3 p2 p5 p1 p6 p0 p7 : Prop)
theorem file78_109905 : (((((False ∨ p3) ∨ (p4 ∨ p6)) → ((p4 ∧ p4) ∧ (p1 ∨ p5))) ∨ (((p5 → False) → False) → False)) → ((((p5 ∧ p2) ∧ (False → False)) ∨ ((p2 ∧ p0) ∧ (p4 → False))) → (((p6 → False) → (True ∧ False)) → ((p7 → False) → (True ∨ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_1
        case inl assump_21 =>
          apply Or.inl
          apply True.intro
        case inr assump_22 =>
          apply Or.inl
          apply True.intro
  case inr assump_10 =>
    cases assump_10
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_1
        case inl assump_37 =>
          apply Or.inl
          apply True.intro
        case inr assump_38 =>
          apply Or.inl
          apply True.intro


variable (p2 p0 p5 p1 p6 : Prop)
theorem file78_110931 : (((((p1 → False) ∧ (False ∧ p6)) → ((True → False) → False)) → (((p0 → p0) ∧ (p2 ∧ False)) ∧ ((p0 → False) → False))) → ((((False → p5) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_28 : (((p1 → False) ∧ (False ∧ p6)) → ((True → False) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
  let assump_7 := assump_1 assump_28
  let assump_20 := And.left assump_7
  let assump_21 := And.right assump_20
  let assump_23 := And.right assump_21
  apply False.elim assump_23


variable (p3 p2 p7 p4 p6 p5 p1 : Prop)
theorem file78_111655 : (((((p3 → True) ∧ (False ∧ p5)) ∧ ((p2 ∨ p3) ∨ (True ∧ p3))) → (((p5 ∧ p5) → False) ∧ ((p7 ∨ p2) → False))) ∨ ((((p5 → False) → (p6 ∧ p1)) → False) ∨ (((p4 → p4) → False) → ((p1 → False) ∧ (p6 ∧ False))))) := by
  apply Or.inl
  intro assump_14
  apply And.intro
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_14
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
  intro assump_32
  cases assump_32
  case inl assump_33 =>
    cases assump_14
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          apply False.elim assump_43
  case inr assump_34 =>
    cases assump_14
    case intro assump_49 assump_50 =>
      cases assump_49
      case intro assump_51 assump_52 =>
        cases assump_52
        case intro assump_55 assump_56 =>
          apply False.elim assump_55


variable (p5 p4 p7 p0 p2 p6 : Prop)
theorem file78_112803 : (((((p7 ∧ p6) → (p2 ∨ p7)) ∨ ((p5 ∧ p0) ∨ (True → False))) → False) → ((((p4 → False) ∧ (p6 ∧ p2)) ∧ ((p5 → False) → False)) ∨ (((p5 ∨ p6) → False) → False))) := by
  intro assump_1
  apply Or.inr
  intro assump_19
  have assump_34 : (((p7 ∧ p6) → (p2 ∨ p7)) ∨ ((p5 ∧ p0) ∨ (True → False))) := by
    apply Or.inl
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      apply Or.inr
      exact assump_25
  let assump_23 := assump_1 assump_34
  apply False.elim assump_23


variable (p3 p6 p1 p4 p5 p2 : Prop)
theorem file78_113363 : (((((p2 ∧ p2) → False) ∧ ((p4 ∨ p5) ∧ (p4 ∧ False))) → False) ∨ ((((p6 → p5) ∧ (p3 ∧ True)) ∧ ((p2 → False) → False)) ∧ (((p4 → True) → False) ∨ ((p2 → p1) ∨ (p4 → p4))))) := by
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
          apply False.elim assump_13
      case inr assump_9 =>
        cases assump_7
        case intro assump_20 assump_21 =>
          apply False.elim assump_21


variable (p4 p1 p3 p5 p7 : Prop)
theorem file78_114015 : (((((p3 → False) → False) → ((p4 ∧ False) → False)) → False) → ((((p1 ∨ p5) → (p4 ∧ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_19 : (((p3 → False) → False) → ((p4 ∧ False) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_7 := assump_1 assump_19
  apply False.elim assump_7


variable (p5 p4 p3 p1 p2 p7 : Prop)
theorem file78_114491 : ((((((p2 ∧ p4) → False) → ((p7 → False) → (p7 ∨ True))) ∨ (((p3 → p4) ∧ (p4 → p5)) ∨ ((False ∧ False) ∧ (p2 → p1)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 ∧ p4) → False) → ((p7 → False) → (p7 ∨ True))) ∨ (((p3 → p4) ∧ (p4 → p5)) ∨ ((False ∧ False) ∧ (p2 → p1)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p2 p7 p5 p1 : Prop)
theorem file78_115004 : (((((p1 ∨ p1) ∧ (p7 → False)) ∧ ((p5 ∨ p7) ∧ (True → False))) → False) ∨ ((((True ∨ p2) ∧ (p5 → False)) ∧ ((p6 → p1) → (True ∧ True))) → False)) := by
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
          cases assump_12
          case inl assump_14 =>
            have assump_56 : True := by
              apply True.intro
            let assump_20 := assump_13 assump_56
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_57 : True := by
              apply True.intro
            let assump_28 := assump_13 assump_57
            apply False.elim assump_28
      case inr assump_7 =>
        cases assump_3
        case intro assump_36 assump_37 =>
          cases assump_36
          case inl assump_38 =>
            have assump_58 : True := by
              apply True.intro
            let assump_44 := assump_37 assump_58
            apply False.elim assump_44
          case inr assump_39 =>
            have assump_59 : True := by
              apply True.intro
            let assump_52 := assump_37 assump_59
            apply False.elim assump_52


variable (p2 p6 p5 p0 p3 p4 : Prop)
theorem file78_116374 : ((((((p5 ∨ p5) ∨ (p0 ∧ p4)) → False) → (((p4 → p3) ∧ (p6 ∧ p5)) → ((p2 ∧ True) → False))) → False) → False) := by
  intro assump_5
  have assump_37 : ((((p5 ∨ p5) ∨ (p0 ∧ p4)) → False) → (((p4 → p3) ∧ (p6 ∧ p5)) → ((p2 ∧ True) → False))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_10
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          have assump_38 : ((p5 ∨ p5) ∨ (p0 ∧ p4)) := by
            apply Or.inl
            apply Or.inl
            exact assump_23
          let assump_30 := assump_9 assump_38
          apply False.elim assump_30
  let assump_8 := assump_5 assump_37
  apply False.elim assump_8


variable (p7 p0 p1 p4 p6 : Prop)
theorem file78_117203 : (((((p6 → p4) ∧ (p4 → p7)) → ((p6 → p1) → (True → False))) ∧ (((True ∨ p7) ∨ (p4 ∧ p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((True ∨ p7) ∨ (p4 ∧ p0)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


