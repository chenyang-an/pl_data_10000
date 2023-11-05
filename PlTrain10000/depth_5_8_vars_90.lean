variable (p3 p1 p5 p2 p6 p7 p0 : Prop)
theorem file90_47 : (((((p0 ∧ p1) ∧ (p3 ∨ p7)) ∧ ((p6 → p7) ∨ (p2 → True))) ∨ (((p2 → False) ∨ (p3 ∨ p7)) → False)) → ((((p3 → p6) ∧ (True → p2)) → ((p6 ∨ True) → False)) → (((p6 → False) → (True ∧ True)) ∨ ((p2 ∨ p3) ∨ (False ∨ p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_10
          case inl assump_17 =>
            cases assump_8
            case inl assump_21 =>
              apply Or.inl
              intro assump_25
              apply And.intro
              apply True.intro
              apply True.intro
            case inr assump_22 =>
              apply Or.inl
              intro assump_28
              apply And.intro
              apply True.intro
              apply True.intro
          case inr assump_18 =>
            cases assump_8
            case inl assump_31 =>
              apply Or.inl
              intro assump_35
              apply And.intro
              apply True.intro
              apply True.intro
            case inr assump_32 =>
              apply Or.inl
              intro assump_38
              apply And.intro
              apply True.intro
              apply True.intro
  case inr assump_6 =>
    apply Or.inl
    intro assump_41
    apply And.intro
    apply True.intro
    apply True.intro


variable (p7 p6 p2 p1 p5 p4 p3 : Prop)
theorem file90_1585 : (((((p5 → False) ∧ (p6 ∧ p3)) → False) ∧ (((True → False) → (p1 → False)) → False)) → ((((p3 ∧ p3) → (p5 ∧ p4)) → ((p6 ∨ p6) → (p2 ∨ p7))) → (((p6 → p2) ∨ (False → p2)) ∨ ((p7 ∧ p3) ∧ (True ∧ p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    apply Or.inl
    intro assump_11
    have assump_29 : ((True → False) → (p1 → False)) := by
      intro assump_16
      intro assump_17
      have assump_30 : True := by
        apply True.intro
      let assump_22 := assump_16 assump_30
      apply False.elim assump_22
    let assump_15 := assump_6 assump_29
    apply False.elim assump_15


variable (p3 p7 p6 p4 p5 : Prop)
theorem file90_2296 : (((((False → False) → (False → p4)) ∧ ((p6 → True) ∧ (True → False))) ∧ (((p5 → p5) → (True → False)) ∨ ((False → False) ∧ (p7 ∨ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case inl assump_14 =>
          have assump_48 : (p5 → p5) := by
            intro assump_19
            exact assump_19
          let assump_18 := assump_14 assump_48
          have assump_49 : True := by
            apply True.intro
          let assump_22 := assump_18 assump_49
          apply False.elim assump_22
        case inr assump_15 =>
          cases assump_15
          case intro assump_26 assump_27 =>
            cases assump_27
            case inl assump_30 =>
              have assump_50 : True := by
                apply True.intro
              let assump_36 := assump_9 assump_50
              apply False.elim assump_36
            case inr assump_31 =>
              have assump_51 : True := by
                apply True.intro
              let assump_44 := assump_9 assump_51
              apply False.elim assump_44


variable (p2 p5 p4 p3 : Prop)
theorem file90_3561 : (((((False ∧ True) ∨ (p2 ∨ p3)) ∨ ((p5 → p4) → (p2 → False))) → False) → False) := by
  intro assump_1
  have assump_20 : (((False ∧ True) ∨ (p2 ∨ p3)) ∨ ((p5 → p4) → (p2 → False))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    have assump_21 : (((False ∧ True) ∨ (p2 ∨ p3)) ∨ ((p5 → p4) → (p2 → False))) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      exact assump_6
    let assump_13 := assump_1 assump_21
    apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p2 p0 p3 p6 p1 p4 p7 p5 : Prop)
theorem file90_4171 : (((((p0 ∧ p6) ∨ (p5 ∨ p2)) ∧ ((p0 ∧ False) → (p1 ∨ True))) ∧ (((True ∧ p0) ∧ (True → p7)) ∧ ((p3 ∨ p7) ∨ (p0 → p2)))) → ((((False → False) → (p2 ∨ p1)) → False) → (((p4 ∨ p4) ∨ (p7 → True)) ∧ ((p7 ∨ p7) ∨ (p0 ∧ True))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_6
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                cases assump_20
                case inl assump_31 =>
                  cases assump_31
                  case inl assump_33 =>
                    apply Or.inr
                    intro assump_37
                    apply True.intro
                  case inr assump_34 =>
                    apply Or.inr
                    intro assump_40
                    apply True.intro
                case inr assump_32 =>
                  apply Or.inr
                  intro assump_43
                  apply True.intro
      case inr assump_10 =>
        cases assump_10
        case inl assump_44 =>
          cases assump_6
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_52
              case intro assump_54 assump_55 =>
                cases assump_51
                case inl assump_62 =>
                  cases assump_62
                  case inl assump_64 =>
                    apply Or.inr
                    intro assump_68
                    apply True.intro
                  case inr assump_65 =>
                    apply Or.inr
                    intro assump_71
                    apply True.intro
                case inr assump_63 =>
                  apply Or.inr
                  intro assump_74
                  apply True.intro
        case inr assump_45 =>
          cases assump_6
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              cases assump_81
              case intro assump_83 assump_84 =>
                cases assump_80
                case inl assump_91 =>
                  cases assump_91
                  case inl assump_93 =>
                    apply Or.inr
                    intro assump_97
                    apply True.intro
                  case inr assump_94 =>
                    apply Or.inr
                    intro assump_100
                    apply True.intro
                case inr assump_92 =>
                  apply Or.inr
                  intro assump_103
                  apply True.intro
  cases assump_1
  case intro assump_106 assump_107 =>
    cases assump_106
    case intro assump_108 assump_109 =>
      cases assump_108
      case inl assump_110 =>
        cases assump_110
        case intro assump_112 assump_113 =>
          cases assump_107
          case intro assump_120 assump_121 =>
            cases assump_120
            case intro assump_122 assump_123 =>
              cases assump_122
              case intro assump_124 assump_125 =>
                cases assump_121
                case inl assump_132 =>
                  cases assump_132
                  case inl assump_134 =>
                    apply Or.inr
                    apply And.intro
                    exact assump_125
                    apply True.intro
                  case inr assump_135 =>
                    apply Or.inl
                    apply Or.inl
                    exact assump_135
                case inr assump_133 =>
                  apply Or.inr
                  apply And.intro
                  exact assump_125
                  apply True.intro
      case inr assump_111 =>
        cases assump_111
        case inl assump_142 =>
          cases assump_107
          case intro assump_148 assump_149 =>
            cases assump_148
            case intro assump_150 assump_151 =>
              cases assump_150
              case intro assump_152 assump_153 =>
                cases assump_149
                case inl assump_160 =>
                  cases assump_160
                  case inl assump_162 =>
                    apply Or.inr
                    apply And.intro
                    exact assump_153
                    apply True.intro
                  case inr assump_163 =>
                    apply Or.inl
                    apply Or.inl
                    exact assump_163
                case inr assump_161 =>
                  apply Or.inr
                  apply And.intro
                  exact assump_153
                  apply True.intro
        case inr assump_143 =>
          cases assump_107
          case intro assump_174 assump_175 =>
            cases assump_174
            case intro assump_176 assump_177 =>
              cases assump_176
              case intro assump_178 assump_179 =>
                cases assump_175
                case inl assump_186 =>
                  cases assump_186
                  case inl assump_188 =>
                    apply Or.inr
                    apply And.intro
                    exact assump_179
                    apply True.intro
                  case inr assump_189 =>
                    apply Or.inl
                    apply Or.inl
                    exact assump_189
                case inr assump_187 =>
                  apply Or.inr
                  apply And.intro
                  exact assump_179
                  apply True.intro


variable (p0 p5 p6 p4 p1 p2 : Prop)
theorem file90_9981 : (((((True → False) ∨ (p1 → p6)) ∨ ((p0 → False) ∧ (p2 ∨ p5))) ∧ (((False → False) ∨ (True ∨ False)) → False)) → ((((False → True) → False) → False) ∧ (((p4 ∧ False) ∨ (False ∧ False)) → ((p2 → False) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_77 : ((False → False) ∨ (True ∨ False)) := by
          apply Or.inl
          intro assump_16
          apply False.elim assump_16
        let assump_15 := assump_6 assump_77
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_78 : ((False → False) ∨ (True ∨ False)) := by
          apply Or.inl
          intro assump_27
          apply False.elim assump_27
        let assump_26 := assump_6 assump_78
        apply False.elim assump_26
    case inr assump_8 =>
      cases assump_8
      case intro assump_33 assump_34 =>
        cases assump_34
        case inl assump_37 =>
          have assump_79 : ((False → False) ∨ (True ∨ False)) := by
            apply Or.inl
            intro assump_44
            apply False.elim assump_44
          let assump_43 := assump_6 assump_79
          apply False.elim assump_43
        case inr assump_38 =>
          have assump_80 : ((False → False) ∨ (True ∨ False)) := by
            apply Or.inl
            intro assump_55
            apply False.elim assump_55
          let assump_54 := assump_6 assump_80
          apply False.elim assump_54
  intro assump_61
  intro assump_62
  cases assump_61
  case inl assump_65 =>
    cases assump_65
    case intro assump_67 assump_68 =>
      apply False.elim assump_68
  case inr assump_66 =>
    cases assump_66
    case intro assump_73 assump_74 =>
      apply False.elim assump_73


variable (p7 p3 p1 p4 p2 p0 p5 p6 : Prop)
theorem file90_11890 : (((((p0 ∧ p7) → (p5 → False)) ∧ ((p2 ∧ p7) → (p3 → p6))) ∧ (((True → False) → (p3 ∨ False)) → False)) → ((((p3 ∧ p1) → (p3 → False)) → ((p2 → p0) → (p0 ∨ p6))) ∧ (((p6 ∧ p4) ∨ (p2 ∨ p7)) → ((False → False) ∨ (p5 ∧ p3))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      have assump_83 : ((True → False) → (p3 ∨ False)) := by
        intro assump_19
        have assump_84 : True := by
          apply True.intro
        let assump_22 := assump_19 assump_84
        apply False.elim assump_22
      let assump_18 := assump_9 assump_83
      apply False.elim assump_18
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_1
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          apply Or.inl
          intro assump_48
          apply False.elim assump_48
  case inr assump_31 =>
    cases assump_31
    case inl assump_51 =>
      cases assump_1
      case intro assump_55 assump_56 =>
        cases assump_55
        case intro assump_57 assump_58 =>
          apply Or.inl
          intro assump_65
          apply False.elim assump_65
    case inr assump_52 =>
      cases assump_1
      case intro assump_70 assump_71 =>
        cases assump_70
        case intro assump_72 assump_73 =>
          apply Or.inl
          intro assump_80
          apply False.elim assump_80


variable (p0 p7 p3 p1 p2 p6 p5 p4 : Prop)
theorem file90_13517 : ((((((p4 → False) ∧ (False ∨ False)) ∧ ((True → False) ∧ (p5 → False))) → (((p6 → p5) ∨ (True ∨ p3)) ∨ ((p7 ∨ p1) → False))) → ((((True ∧ p2) → (p5 ∨ True)) → False) ∧ (((p3 ∧ p0) ∨ (p5 → False)) → False))) → False) := by
  intro assump_9
  have assump_38 : ((((p4 → False) ∧ (False ∨ False)) ∧ ((True → False) ∧ (p5 → False))) → (((p6 → p5) ∨ (True ∨ p3)) ∨ ((p7 ∨ p1) → False))) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_17
        case inl assump_20 =>
          apply False.elim assump_20
        case inr assump_21 =>
          apply False.elim assump_21
  let assump_12 := assump_9 assump_38
  let assump_26 := And.left assump_12
  have assump_39 : ((True ∧ p2) → (p5 ∨ True)) := by
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      apply Or.inr
      apply True.intro
  let assump_27 := assump_26 assump_39
  apply False.elim assump_27


variable (p6 p0 p5 p4 : Prop)
theorem file90_14573 : (((((p6 ∧ p5) → (p0 ∨ False)) → ((False → True) ∧ (p5 → False))) ∧ (((p4 ∧ p4) → False) ∧ ((p5 → False) ∧ (p6 ∧ p4)))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_16
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        cases assump_24
        case intro assump_27 assump_28 =>
          have assump_40 : (p4 ∧ p4) := by
            apply And.intro
            exact assump_28
            exact assump_28
          let assump_36 := assump_19 assump_40
          apply False.elim assump_36


variable (p6 p4 p1 p5 p7 p3 p0 : Prop)
theorem file90_15239 : (((((p5 → False) ∨ (p6 → False)) ∧ ((True ∨ p1) ∧ (False ∧ False))) ∧ (((p5 ∧ p3) → False) ∨ ((p7 → p1) ∨ (p4 → p0)))) → ((((p4 ∧ p0) ∧ (p3 → p0)) → ((p0 → False) → (False ∧ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
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
      case inr assump_10 =>
        cases assump_8
        case intro assump_31 assump_32 =>
          cases assump_31
          case inl assump_33 =>
            cases assump_32
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
          case inr assump_34 =>
            cases assump_32
            case intro assump_43 assump_44 =>
              apply False.elim assump_43


variable (p1 p3 p4 p0 p5 p6 : Prop)
theorem file90_16481 : (((((p1 ∨ p1) ∨ (False → p0)) ∨ ((p4 → False) → False)) ∨ (((p3 → p0) → (p6 ∨ p0)) ∧ ((p3 → False) ∨ (p1 → False)))) ∧ ((((p3 → True) → False) ∧ ((p6 → False) ∨ (p3 ∧ p5))) → False)) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply False.elim assump_1
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_32 : (p3 → True) := by
        intro assump_15
        apply True.intro
      let assump_14 := assump_5 assump_32
      apply False.elim assump_14
    case inr assump_10 =>
      cases assump_10
      case intro assump_19 assump_20 =>
        have assump_33 : (p3 → True) := by
          intro assump_28
          apply True.intro
        let assump_27 := assump_5 assump_33
        apply False.elim assump_27


variable (p4 p7 p3 p2 p1 p5 : Prop)
theorem file90_17378 : (((((p1 → False) ∨ (p3 → p5)) ∧ ((p2 ∧ p7) ∨ (False ∨ True))) ∧ (((p3 → True) → False) ∧ ((True ∨ p7) ∨ (p4 → p4)))) → False) := by
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
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                cases assump_22
                case inl assump_24 =>
                  have assump_164 : (p3 → True) := by
                    intro assump_29
                    apply True.intro
                  let assump_28 := assump_18 assump_164
                  apply False.elim assump_28
                case inr assump_25 =>
                  have assump_165 : (p3 → True) := by
                    intro assump_37
                    apply True.intro
                  let assump_36 := assump_18 assump_165
                  apply False.elim assump_36
              case inr assump_23 =>
                have assump_166 : (p3 → True) := by
                  intro assump_45
                  apply True.intro
                let assump_44 := assump_18 assump_166
                apply False.elim assump_44
        case inr assump_11 =>
          cases assump_11
          case inl assump_49 =>
            apply False.elim assump_49
          case inr assump_50 =>
            cases assump_3
            case intro assump_55 assump_56 =>
              cases assump_56
              case inl assump_59 =>
                cases assump_59
                case inl assump_61 =>
                  have assump_167 : (p3 → True) := by
                    intro assump_66
                    apply True.intro
                  let assump_65 := assump_55 assump_167
                  apply False.elim assump_65
                case inr assump_62 =>
                  have assump_168 : (p3 → True) := by
                    intro assump_74
                    apply True.intro
                  let assump_73 := assump_55 assump_168
                  apply False.elim assump_73
              case inr assump_60 =>
                have assump_169 : (p3 → True) := by
                  intro assump_82
                  apply True.intro
                let assump_81 := assump_55 assump_169
                apply False.elim assump_81
      case inr assump_7 =>
        cases assump_5
        case inl assump_88 =>
          cases assump_88
          case intro assump_90 assump_91 =>
            cases assump_3
            case intro assump_96 assump_97 =>
              cases assump_97
              case inl assump_100 =>
                cases assump_100
                case inl assump_102 =>
                  have assump_170 : (p3 → True) := by
                    intro assump_107
                    apply True.intro
                  let assump_106 := assump_96 assump_170
                  apply False.elim assump_106
                case inr assump_103 =>
                  have assump_171 : (p3 → True) := by
                    intro assump_115
                    apply True.intro
                  let assump_114 := assump_96 assump_171
                  apply False.elim assump_114
              case inr assump_101 =>
                have assump_172 : (p3 → True) := by
                  intro assump_123
                  apply True.intro
                let assump_122 := assump_96 assump_172
                apply False.elim assump_122
        case inr assump_89 =>
          cases assump_89
          case inl assump_127 =>
            apply False.elim assump_127
          case inr assump_128 =>
            cases assump_3
            case intro assump_133 assump_134 =>
              cases assump_134
              case inl assump_137 =>
                cases assump_137
                case inl assump_139 =>
                  have assump_173 : (p3 → True) := by
                    intro assump_144
                    apply True.intro
                  let assump_143 := assump_133 assump_173
                  apply False.elim assump_143
                case inr assump_140 =>
                  have assump_174 : (p3 → True) := by
                    intro assump_152
                    apply True.intro
                  let assump_151 := assump_133 assump_174
                  apply False.elim assump_151
              case inr assump_138 =>
                have assump_175 : (p3 → True) := by
                  intro assump_160
                  apply True.intro
                let assump_159 := assump_133 assump_175
                apply False.elim assump_159


variable (p3 p6 p2 p5 p1 p0 p4 : Prop)
theorem file90_22200 : (((((True → False) → False) → ((p4 → p4) ∨ (p0 → False))) ∨ (((False ∧ p3) → (p6 ∨ p3)) → False)) ∨ ((((True ∧ p1) → False) → ((True ∧ p0) → (p3 → False))) ∧ (((p2 → p6) ∧ (p2 ∨ p1)) → ((p5 → p1) ∧ (False → p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_28
  apply Or.inl
  intro assump_31
  exact assump_31


variable (p3 p6 p1 : Prop)
theorem file90_22571 : (((((p3 ∨ p6) → (False → False)) ∨ ((p1 → False) ∧ (True → p3))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p3 ∨ p6) → (False → False)) ∨ ((p1 → False) ∧ (True → p3))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p7 p0 p5 p4 p3 : Prop)
theorem file90_22975 : (((((p5 ∧ True) → (p3 → p5)) ∨ ((p7 ∧ True) → False)) → False) → ((((False ∧ p0) ∧ (p4 → p4)) → False) ∧ (((p2 → False) → False) ∨ ((p2 ∧ p7) ∧ (p7 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  apply Or.inl
  intro assump_11
  have assump_29 : (((p5 ∧ True) → (p3 → p5)) ∨ ((p7 ∧ True) → False)) := by
    apply Or.inl
    intro assump_16
    intro assump_17
    cases assump_16
    case intro assump_20 assump_21 =>
      exact assump_20
  let assump_15 := assump_1 assump_29
  apply False.elim assump_15


variable (p5 p2 p4 p7 p3 : Prop)
theorem file90_23703 : (((((True ∨ p4) ∧ (False → p5)) → False) → (((p7 ∨ p3) ∧ (False → False)) ∧ ((p4 → False) ∧ (p2 → False)))) → ((((p7 ∧ p5) ∧ (False ∧ p5)) ∧ ((p3 → p5) → False)) → False)) := by
  intro assump_11
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_16
        case intro assump_23 assump_24 =>
          apply False.elim assump_23


variable (p0 p6 p3 : Prop)
theorem file90_24245 : (((((p6 ∧ p3) ∧ (p0 → False)) → ((p0 ∨ p0) → False)) → False) → False) := by
  intro assump_1
  have assump_44 : (((p6 ∧ p3) ∧ (p0 → False)) → ((p0 ∨ p0) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_45 : p0 := by
            exact assump_7
          let assump_21 := assump_12 assump_45
          apply False.elim assump_21
    case inr assump_8 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          have assump_46 : p0 := by
            exact assump_8
          let assump_37 := assump_28 assump_46
          apply False.elim assump_37
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p5 p6 p4 : Prop)
theorem file90_25186 : ((((((p4 → True) ∨ (p5 ∧ p6)) → False) → False) → False) → False) := by
  intro assump_10
  have assump_25 : ((((p4 → True) ∨ (p5 ∧ p6)) → False) → False) := by
    intro assump_14
    have assump_26 : ((p4 → True) ∨ (p5 ∧ p6)) := by
      apply Or.inl
      intro assump_18
      apply True.intro
    let assump_17 := assump_14 assump_26
    apply False.elim assump_17
  let assump_13 := assump_10 assump_25
  apply False.elim assump_13


variable (p3 p4 p1 : Prop)
theorem file90_25675 : (((((p3 ∨ p3) ∧ (p3 → False)) ∧ ((p1 → False) ∧ (p3 → False))) → False) ∧ ((((False → False) ∨ (p1 ∨ p3)) → ((False → False) → False)) → (((False ∨ p4) ∧ (False ∧ False)) ∧ ((True → False) → False)))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          have assump_92 : p3 := by
            exact assump_6
          let assump_18 := assump_13 assump_92
          apply False.elim assump_18
      case inr assump_7 =>
        cases assump_3
        case intro assump_26 assump_27 =>
          have assump_93 : p3 := by
            exact assump_7
          let assump_32 := assump_27 assump_93
          apply False.elim assump_32
  intro assump_36
  apply And.intro
  apply And.intro
  have assump_94 : ((False → False) ∨ (p1 ∨ p3)) := by
    apply Or.inl
    intro assump_40
    apply False.elim assump_40
  let assump_39 := assump_36 assump_94
  have assump_95 : (False → False) := by
    intro assump_44
    apply False.elim assump_44
  let assump_43 := assump_39 assump_95
  apply False.elim assump_43
  apply And.intro
  have assump_96 : ((False → False) ∨ (p1 ∨ p3)) := by
    apply Or.inl
    intro assump_53
    apply False.elim assump_53
  let assump_52 := assump_36 assump_96
  have assump_97 : (False → False) := by
    intro assump_57
    apply False.elim assump_57
  let assump_56 := assump_52 assump_97
  apply False.elim assump_56
  have assump_98 : ((False → False) ∨ (p1 ∨ p3)) := by
    apply Or.inl
    intro assump_66
    apply False.elim assump_66
  let assump_65 := assump_36 assump_98
  have assump_99 : (False → False) := by
    intro assump_70
    apply False.elim assump_70
  let assump_69 := assump_65 assump_99
  apply False.elim assump_69
  intro assump_76
  have assump_100 : ((False → False) ∨ (p1 ∨ p3)) := by
    apply Or.inl
    intro assump_82
    apply False.elim assump_82
  let assump_81 := assump_36 assump_100
  have assump_101 : (False → False) := by
    intro assump_86
    apply False.elim assump_86
  let assump_85 := assump_81 assump_101
  apply False.elim assump_85


variable (p1 p7 p5 p4 p3 p0 : Prop)
theorem file90_27964 : (((((p7 ∨ p1) ∧ (p0 ∨ p4)) ∧ ((p7 → False) → (p5 ∧ p0))) → False) → ((((p7 ∨ True) → False) → ((p5 ∨ p3) ∨ (p4 → False))) ∨ (((p0 ∧ True) → (p4 → False)) ∧ ((True → p5) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inr
  intro assump_7
  have assump_15 : (p7 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_11 := assump_4 assump_15
  apply False.elim assump_11


variable (p0 p6 p3 p2 p1 : Prop)
theorem file90_28431 : (((((p3 ∨ p1) ∧ (p1 ∧ p1)) → ((False ∧ p2) → (False ∨ p0))) → False) → ((((p6 → p3) → (False ∨ p6)) → False) → (((p6 → False) ∨ (p1 ∨ p6)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    have assump_56 : (((p3 ∨ p1) ∧ (p1 ∧ p1)) → ((False ∧ p2) → (False ∨ p0))) := by
      intro assump_13
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
    let assump_12 := assump_1 assump_56
    apply False.elim assump_12
  case inr assump_5 =>
    cases assump_5
    case inl assump_22 =>
      have assump_57 : (((p3 ∨ p1) ∧ (p1 ∧ p1)) → ((False ∧ p2) → (False ∨ p0))) := by
        intro assump_31
        intro assump_32
        cases assump_32
        case intro assump_33 assump_34 =>
          apply False.elim assump_33
      let assump_30 := assump_1 assump_57
      apply False.elim assump_30
    case inr assump_23 =>
      have assump_58 : (((p3 ∨ p1) ∧ (p1 ∧ p1)) → ((False ∧ p2) → (False ∨ p0))) := by
        intro assump_47
        intro assump_48
        cases assump_48
        case intro assump_49 assump_50 =>
          apply False.elim assump_49
      let assump_46 := assump_1 assump_58
      apply False.elim assump_46


variable (p2 p5 p0 p7 p1 : Prop)
theorem file90_29752 : (((((p2 ∧ p7) ∧ (True → p0)) ∧ ((p2 → False) → (False ∨ p1))) → (((p7 → p1) → False) → ((False ∧ p5) → False))) → ((((p0 → p2) → (p5 → True)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : ((p0 → p2) → (p5 → True)) := by
    intro assump_9
    intro assump_10
    apply True.intro
  let assump_8 := assump_2 assump_14
  apply False.elim assump_8


variable (p5 p7 p1 p4 : Prop)
theorem file90_30183 : ((((((False → False) ∨ (p7 → p7)) ∨ ((p7 ∧ p4) → (p1 ∨ p5))) ∨ (((p4 ∧ p5) ∧ (False → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (p7 → p7)) ∨ ((p7 ∧ p4) → (p1 ∨ p5))) ∨ (((p4 ∧ p5) ∧ (False → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p3 p7 p6 p0 p5 : Prop)
theorem file90_30680 : (((((False ∧ False) ∧ (p6 ∧ False)) ∧ ((p0 → p2) ∧ (p0 ∧ p2))) ∧ (((p3 ∧ p7) ∨ (True ∨ p6)) ∨ ((p5 → p7) → (p2 → False)))) → False) := by
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


variable (p3 p0 p5 p1 p4 p7 : Prop)
theorem file90_31159 : (((((p5 → p5) → (p7 → True)) → ((p4 → False) → (True ∨ p0))) → False) → ((((p7 → p7) ∨ (False → p3)) → False) → (((p1 ∧ p3) → (False ∨ p1)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_20 : (((p5 → p5) → (p7 → True)) → ((p4 → False) → (True ∨ p0))) := by
    intro assump_11
    intro assump_12
    apply Or.inl
    apply True.intro
  let assump_10 := assump_1 assump_20
  apply False.elim assump_10


variable (p6 p1 p4 p3 p0 p5 p7 p2 : Prop)
theorem file90_31662 : (((((p2 → p6) → (p5 ∨ p6)) ∨ ((p1 → p7) ∧ (p4 ∧ p2))) → False) → ((((p4 → True) ∧ (p7 → False)) → ((p0 → True) ∨ (p3 ∧ p3))) ∨ (((p3 → p1) → (p3 ∧ p2)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    apply True.intro


variable (p2 p6 p3 p0 p7 : Prop)
theorem file90_32046 : ((((((p0 → False) → False) → False) → (((p2 ∨ True) ∨ (p6 → False)) ∨ ((p7 → p0) ∨ (p3 → False)))) → False) → False) := by
  intro assump_15
  have assump_25 : ((((p0 → False) → False) → False) → (((p2 ∨ True) ∨ (p6 → False)) ∨ ((p7 → p0) ∨ (p3 → False)))) := by
    intro assump_19
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_18 := assump_15 assump_25
  apply False.elim assump_18


variable (p4 p1 p7 p2 p5 p3 p0 : Prop)
theorem file90_32532 : (((((p7 ∨ p4) ∨ (p4 → p3)) → False) → False) ∧ ((((p2 → False) → (p4 → p0)) → ((p1 ∧ p1) ∨ (p5 → p5))) ∧ (((p1 → p0) ∨ (p0 → False)) → ((False → p1) ∧ (False → False))))) := by
  apply And.intro
  intro assump_1
  have assump_29 : ((p7 ∨ p4) ∨ (p4 → p3)) := by
    apply Or.inr
    intro assump_5
    have assump_30 : ((p7 ∨ p4) ∨ (p4 → p3)) := by
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_30
    apply False.elim assump_9
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4
  apply And.intro
  intro assump_16
  apply Or.inr
  intro assump_19
  exact assump_19
  intro assump_22
  apply And.intro
  intro assump_23
  apply False.elim assump_23
  intro assump_26
  apply False.elim assump_26


variable (p3 p4 p6 : Prop)
theorem file90_33341 : ((((((p6 ∧ p4) ∨ (False ∨ p4)) ∧ ((p3 ∨ p3) → (False → False))) → (((False → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_51 : ((((p6 ∧ p4) ∨ (False ∨ p4)) ∧ ((p3 ∨ p3) → (False → False))) → (((False → False) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_52 : (False → False) := by
            intro assump_25
            apply False.elim assump_25
          let assump_24 := assump_6 assump_52
          apply False.elim assump_24
      case inr assump_12 =>
        cases assump_12
        case inl assump_31 =>
          apply False.elim assump_31
        case inr assump_32 =>
          have assump_53 : (False → False) := by
            intro assump_42
            apply False.elim assump_42
          let assump_41 := assump_6 assump_53
          apply False.elim assump_41
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p2 p7 p6 p0 p5 p3 p4 : Prop)
theorem file90_34495 : (((((p4 → p6) ∧ (p0 ∨ p4)) → ((False → False) ∧ (p0 → p5))) → (((p2 → False) ∨ (False → False)) → ((False ∧ p3) → (p7 ∨ p7)))) ∧ ((((p7 → p5) → (p3 → p5)) ∧ ((p3 → p5) ∨ (p6 → True))) → (((p6 → p5) ∧ (p7 ∧ p0)) → ((True → p0) ∨ (False ∧ p7))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  intro assump_8
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_8
      case intro assump_20 assump_21 =>
        cases assump_21
        case inl assump_24 =>
          apply Or.inl
          intro assump_28
          exact assump_15
        case inr assump_25 =>
          apply Or.inl
          intro assump_33
          exact assump_15


variable (p3 p1 p4 p5 p0 p7 : Prop)
theorem file90_35396 : ((((((p1 → True) ∨ (p4 ∨ p3)) ∨ ((p1 ∧ p0) ∨ (False → False))) ∨ (((p5 ∧ p7) ∨ (p7 → p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p1 → True) ∨ (p4 ∨ p3)) ∨ ((p1 ∧ p0) ∨ (False → False))) ∨ (((p5 ∧ p7) ∨ (p7 → p1)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p7 : Prop)
theorem file90_35862 : (((((p7 ∧ False) ∨ (p2 → False)) → ((False ∧ p7) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : (((p7 ∧ False) ∨ (p2 → False)) → ((False ∧ p7) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p0 p2 p6 p1 p5 p7 : Prop)
theorem file90_36297 : ((((((True ∧ p5) ∨ (p5 ∧ p7)) ∧ ((False → p2) → False)) → (((p6 ∨ p0) ∨ (p1 ∨ False)) ∨ ((False ∧ p0) → (p3 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((True ∧ p5) ∨ (p5 ∧ p7)) ∧ ((False → p2) → False)) → (((p6 ∨ p0) ∨ (p1 ∨ False)) ∨ ((False ∧ p0) → (p3 ∨ p1)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inr
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
      case inr assump_9 =>
        cases assump_9
        case intro assump_23 assump_24 =>
          apply Or.inr
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p2 p6 p1 p5 p3 p0 p4 p7 : Prop)
theorem file90_37321 : (((((p0 ∨ True) → (p5 ∨ p4)) → ((p1 ∧ p1) → (p7 ∨ p3))) ∨ (((p6 ∨ p3) ∨ (True → False)) ∨ ((p1 → False) → False))) → ((((False → False) → False) → False) ∨ (((p0 ∧ p7) ∨ (False → p4)) ∨ ((p2 → False) ∧ (p2 ∨ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_70 : (False → False) := by
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_6 assump_70
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case inl assump_16 =>
      cases assump_16
      case inl assump_18 =>
        cases assump_18
        case inl assump_20 =>
          apply Or.inl
          intro assump_24
          have assump_71 : (False → False) := by
            intro assump_28
            apply False.elim assump_28
          let assump_27 := assump_24 assump_71
          apply False.elim assump_27
        case inr assump_21 =>
          apply Or.inl
          intro assump_36
          have assump_72 : (False → False) := by
            intro assump_40
            apply False.elim assump_40
          let assump_39 := assump_36 assump_72
          apply False.elim assump_39
      case inr assump_19 =>
        apply Or.inl
        intro assump_48
        have assump_73 : (False → False) := by
          intro assump_52
          apply False.elim assump_52
        let assump_51 := assump_48 assump_73
        apply False.elim assump_51
    case inr assump_17 =>
      apply Or.inl
      intro assump_60
      have assump_74 : (False → False) := by
        intro assump_64
        apply False.elim assump_64
      let assump_63 := assump_60 assump_74
      apply False.elim assump_63


variable (p1 p3 p6 p5 p2 p4 p0 : Prop)
theorem file90_39079 : (((((p4 ∨ p0) → False) ∨ ((False → p0) ∨ (p2 ∨ p5))) → (((p5 ∧ p1) → (False ∧ p6)) ∨ ((p6 → False) ∧ (p3 → p0)))) → ((((p5 → True) ∧ (p3 → p4)) → False) → (((False ∨ p6) ∨ (p5 ∨ True)) ∨ ((p5 → p0) ∧ (False → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p3 p1 p4 p2 p0 p7 : Prop)
theorem file90_39463 : (((((p0 → False) ∧ (p0 → False)) ∧ ((p4 ∨ p2) ∨ (True → p7))) → False) → ((((p4 → False) ∧ (p0 ∧ False)) ∧ ((p1 → False) → (p2 → False))) → (((p1 → False) → (p3 ∧ True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        apply False.elim assump_13


variable (p7 p1 p6 p0 p5 p2 : Prop)
theorem file90_39963 : ((((((p5 ∨ False) ∧ (p1 → True)) ∨ ((p2 → True) → (p0 ∨ True))) ∨ (((p7 ∧ p1) → (p6 ∧ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 ∨ False) ∧ (p1 → True)) ∨ ((p2 → True) → (p0 ∨ True))) ∨ (((p7 ∧ p1) → (p6 ∧ True)) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p6 p4 p2 p0 p1 p3 p5 : Prop)
theorem file90_40455 : (((((False → p6) ∧ (p5 ∨ p6)) → False) ∧ (((p4 ∧ p7) ∧ (p3 ∧ True)) → False)) → ((((p2 ∧ False) → False) ∧ ((p5 ∨ True) → False)) → (((False ∧ p4) ∧ (p7 → False)) ∧ ((p5 ∨ p1) ∨ (p1 → p0))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      have assump_94 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_20 := assump_4 assump_94
      apply False.elim assump_20
  cases assump_2
  case intro assump_24 assump_25 =>
    cases assump_1
    case intro assump_30 assump_31 =>
      have assump_95 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_41 := assump_25 assump_95
      apply False.elim assump_41
  intro assump_45
  cases assump_2
  case intro assump_48 assump_49 =>
    cases assump_1
    case intro assump_54 assump_55 =>
      have assump_96 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_65 := assump_49 assump_96
      apply False.elim assump_65
  cases assump_2
  case intro assump_69 assump_70 =>
    cases assump_1
    case intro assump_75 assump_76 =>
      apply Or.inr
      intro assump_81
      have assump_97 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_90 := assump_70 assump_97
      apply False.elim assump_90


variable (p4 p2 p5 p0 p3 p6 p1 : Prop)
theorem file90_41951 : (((((True → False) ∧ (True ∧ p4)) → ((p5 ∧ p6) ∨ (p0 → False))) ∨ (((p3 ∨ p0) → (True ∨ p2)) ∧ ((p2 ∧ p1) ∨ (p1 ∧ p3)))) ∨ ((((True ∧ p5) → False) ∧ ((p3 → False) → (p1 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inr
      intro assump_12
      have assump_21 : True := by
        apply True.intro
      let assump_17 := assump_2 assump_21
      apply False.elim assump_17


variable (p3 p0 p7 p4 p6 : Prop)
theorem file90_42532 : ((((((p3 ∨ False) → False) ∧ ((p0 → p7) → (p6 → True))) → False) ∧ ((((True → False) → (p0 → p3)) ∨ ((p4 ∨ False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((True → False) → (p0 → p3)) ∨ ((p4 ∨ False) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      have assump_23 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_23
      apply False.elim assump_15
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p5 p4 p0 p3 p7 p1 p2 : Prop)
theorem file90_43160 : ((((((p1 → False) ∨ (p5 → p4)) ∨ ((p0 ∨ False) → (p2 → False))) ∧ (((p3 → False) → False) ∨ ((False → p2) ∨ (p4 → False)))) ∧ ((((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) → False)) → False) := by
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
            have assump_172 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
              intro assump_19
              intro assump_20
              apply And.intro
              cases assump_20
              case intro assump_21 assump_22 =>
                apply False.elim assump_22
              apply True.intro
            let assump_18 := assump_3 assump_172
            apply False.elim assump_18
          case inr assump_13 =>
            cases assump_13
            case inl assump_30 =>
              have assump_173 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
                intro assump_37
                intro assump_38
                apply And.intro
                cases assump_38
                case intro assump_39 assump_40 =>
                  apply False.elim assump_40
                apply True.intro
              let assump_36 := assump_3 assump_173
              apply False.elim assump_36
            case inr assump_31 =>
              have assump_174 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
                intro assump_53
                intro assump_54
                apply And.intro
                cases assump_54
                case intro assump_55 assump_56 =>
                  apply False.elim assump_56
                apply True.intro
              let assump_52 := assump_3 assump_174
              apply False.elim assump_52
        case inr assump_9 =>
          cases assump_5
          case inl assump_66 =>
            have assump_175 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
              intro assump_73
              intro assump_74
              apply And.intro
              cases assump_74
              case intro assump_75 assump_76 =>
                apply False.elim assump_76
              apply True.intro
            let assump_72 := assump_3 assump_175
            apply False.elim assump_72
          case inr assump_67 =>
            cases assump_67
            case inl assump_84 =>
              have assump_176 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
                intro assump_91
                intro assump_92
                apply And.intro
                cases assump_92
                case intro assump_93 assump_94 =>
                  apply False.elim assump_94
                apply True.intro
              let assump_90 := assump_3 assump_176
              apply False.elim assump_90
            case inr assump_85 =>
              have assump_177 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
                intro assump_107
                intro assump_108
                apply And.intro
                cases assump_108
                case intro assump_109 assump_110 =>
                  apply False.elim assump_110
                apply True.intro
              let assump_106 := assump_3 assump_177
              apply False.elim assump_106
      case inr assump_7 =>
        cases assump_5
        case inl assump_120 =>
          have assump_178 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
            intro assump_127
            intro assump_128
            apply And.intro
            cases assump_128
            case intro assump_129 assump_130 =>
              apply False.elim assump_130
            apply True.intro
          let assump_126 := assump_3 assump_178
          apply False.elim assump_126
        case inr assump_121 =>
          cases assump_121
          case inl assump_138 =>
            have assump_179 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
              intro assump_145
              intro assump_146
              apply And.intro
              cases assump_146
              case intro assump_147 assump_148 =>
                apply False.elim assump_148
              apply True.intro
            let assump_144 := assump_3 assump_179
            apply False.elim assump_144
          case inr assump_139 =>
            have assump_180 : (((p5 → p2) → (False ∧ False)) → ((p7 ∧ False) → (p1 ∧ True))) := by
              intro assump_161
              intro assump_162
              apply And.intro
              cases assump_162
              case intro assump_163 assump_164 =>
                apply False.elim assump_164
              apply True.intro
            let assump_160 := assump_3 assump_180
            apply False.elim assump_160


variable (p0 p7 p6 p2 : Prop)
theorem file90_48209 : (((((p7 ∧ True) ∨ (p7 → False)) ∨ ((p0 → p2) ∧ (p6 ∧ p2))) ∧ (((p6 → p6) → False) ∧ ((p7 → False) ∨ (p6 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case inl assump_18 =>
              have assump_96 : p7 := by
                exact assump_8
              let assump_22 := assump_18 assump_96
              apply False.elim assump_22
            case inr assump_19 =>
              have assump_97 : (p6 → p6) := by
                intro assump_30
                exact assump_30
              let assump_29 := assump_14 assump_97
              apply False.elim assump_29
      case inr assump_7 =>
        cases assump_3
        case intro assump_38 assump_39 =>
          cases assump_39
          case inl assump_42 =>
            have assump_98 : (p6 → p6) := by
              intro assump_48
              exact assump_48
            let assump_47 := assump_38 assump_98
            apply False.elim assump_47
          case inr assump_43 =>
            have assump_99 : (p6 → p6) := by
              intro assump_58
              exact assump_58
            let assump_57 := assump_38 assump_99
            apply False.elim assump_57
    case inr assump_5 =>
      cases assump_5
      case intro assump_64 assump_65 =>
        cases assump_65
        case intro assump_68 assump_69 =>
          cases assump_3
          case intro assump_74 assump_75 =>
            cases assump_75
            case inl assump_78 =>
              have assump_100 : (p6 → p6) := by
                intro assump_84
                exact assump_84
              let assump_83 := assump_74 assump_100
              apply False.elim assump_83
            case inr assump_79 =>
              have assump_101 : p6 := by
                exact assump_68
              let assump_92 := assump_79 assump_101
              apply False.elim assump_92


variable (p2 p1 p6 p4 p0 p5 p7 : Prop)
theorem file90_50413 : (((((p1 ∧ False) → (p2 → False)) → False) → False) ∧ ((((p4 → p5) → False) → ((p4 → p6) → (p5 ∨ True))) ∧ (((p7 → True) ∨ (p1 ∨ p0)) → ((p7 → True) ∨ (p0 ∨ p0))))) := by
  apply And.intro
  intro assump_1
  have assump_38 : ((p1 ∧ False) → (p2 → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4
  apply And.intro
  intro assump_18
  intro assump_19
  apply Or.inr
  apply True.intro
  intro assump_24
  cases assump_24
  case inl assump_25 =>
    apply Or.inl
    intro assump_29
    apply True.intro
  case inr assump_26 =>
    cases assump_26
    case inl assump_30 =>
      apply Or.inl
      intro assump_34
      apply True.intro
    case inr assump_31 =>
      apply Or.inl
      intro assump_37
      apply True.intro


variable (p2 p6 p7 p1 p5 p3 : Prop)
theorem file90_51355 : (((((p7 ∨ p6) ∧ (p1 → False)) → False) → (((p3 → p3) → False) → False)) ∨ ((((False ∧ False) ∧ (p5 ∨ p6)) ∧ ((False ∨ p3) → False)) ∧ (((p7 ∨ p2) → (p7 → p5)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_15 : (p3 → p3) := by
    intro assump_9
    exact assump_9
  let assump_8 := assump_2 assump_15
  apply False.elim assump_8


variable (p5 p4 p2 p6 p3 p1 p7 : Prop)
theorem file90_51781 : (((((p4 → p4) ∨ (True ∧ p4)) → False) → False) ∨ ((((p6 → p6) → (p7 → True)) ∧ ((p1 → p3) → False)) ∧ (((p4 ∨ p5) ∨ (p2 → False)) → ((True ∨ p6) → (p2 → p3))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p4 → p4) ∨ (True ∧ p4)) := by
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p6 p2 p1 : Prop)
theorem file90_52205 : ((((((False ∧ False) → False) ∧ ((False ∧ p5) ∧ (False ∨ p6))) → (((p5 → False) → False) ∧ ((True ∨ True) ∧ (p1 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_52 : ((((False ∧ False) → False) ∧ ((False ∧ p5) ∧ (False ∨ p6))) → (((p5 → False) → False) ∧ ((True ∨ True) ∧ (p1 ∧ p2)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
    apply And.intro
    cases assump_5
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
    apply And.intro
    cases assump_5
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          apply False.elim assump_35
    cases assump_5
    case intro assump_39 assump_40 =>
      cases assump_40
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          apply False.elim assump_45
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p2 p3 p6 p5 p4 : Prop)
theorem file90_53618 : (((((True → False) → (p2 ∨ False)) ∨ ((p3 ∧ p3) ∧ (p3 → False))) ∧ (((p5 → True) → False) → False)) ∨ ((((p6 → p4) ∨ (p3 ∨ p2)) → False) → False)) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_16 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4
  intro assump_8
  have assump_17 : (p5 → True) := by
    intro assump_12
    apply True.intro
  let assump_11 := assump_8 assump_17
  apply False.elim assump_11


variable (p1 p7 p4 p6 p3 p5 : Prop)
theorem file90_54174 : (((((p6 ∨ p7) ∨ (p5 → False)) → ((p4 ∧ False) → (p3 ∧ p1))) ∧ (((p3 ∧ p3) → (p3 ∨ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p3 ∧ p3) → (p3 ∨ p4)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        exact assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p2 p5 p1 p4 p6 p3 p0 p7 : Prop)
theorem file90_54667 : (((((True → p0) ∧ (p7 → False)) ∧ ((p4 → False) → (False → False))) → (((False ∧ p2) ∨ (p5 → True)) → ((p5 → p1) ∨ (p6 ∧ p2)))) → ((((p3 ∨ p0) ∨ (p6 → p6)) ∨ ((p6 ∨ p4) → (p5 ∧ p7))) ∨ (((False ∧ p4) ∨ (p2 ∨ True)) → ((p4 → False) → (False → p2))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_4
  exact assump_4


variable (p3 p6 p5 p2 p4 p7 : Prop)
theorem file90_55079 : (((((p5 → p5) ∨ (p6 → False)) → False) → False) ∨ ((((p2 ∨ p3) ∨ (p3 → p7)) ∨ ((p3 ∨ p6) ∨ (p4 ∧ p3))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p5 → p5) ∨ (p6 → False)) := by
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p3 p0 p2 p7 p6 p1 : Prop)
theorem file90_55465 : ((((((p3 ∧ p6) ∨ (p2 → True)) ∨ ((p7 ∧ p5) ∧ (p0 → False))) ∨ (((p0 → False) → False) ∨ ((p7 → False) → (False ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p3 ∧ p6) ∨ (p2 → True)) ∨ ((p7 ∧ p5) ∧ (p0 → False))) ∨ (((p0 → False) → False) ∨ ((p7 → False) → (False ∧ p1)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p3 p7 p1 p5 p4 p0 p6 p2 : Prop)
theorem file90_55989 : (((((p5 → p4) ∨ (p4 → p7)) → ((p5 ∧ p1) ∨ (p5 → p0))) ∨ (((p0 ∧ p1) → (p1 → p3)) ∨ ((False → p0) ∨ (p4 ∨ True)))) → ((((True → False) → (p0 → False)) → ((p3 → p6) → (p2 ∨ True))) ∧ (((p2 → False) ∧ (p1 ∧ p1)) → ((p0 ∨ p1) ∨ (p2 → True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    apply Or.inr
    apply True.intro
  case inr assump_9 =>
    cases assump_9
    case inl assump_12 =>
      apply Or.inr
      apply True.intro
    case inr assump_13 =>
      cases assump_13
      case inl assump_16 =>
        apply Or.inr
        apply True.intro
      case inr assump_17 =>
        cases assump_17
        case inl assump_20 =>
          apply Or.inr
          apply True.intro
        case inr assump_21 =>
          apply Or.inr
          apply True.intro
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_28
    case intro assump_31 assump_32 =>
      cases assump_1
      case inl assump_37 =>
        apply Or.inl
        apply Or.inr
        exact assump_32
      case inr assump_38 =>
        cases assump_38
        case inl assump_41 =>
          apply Or.inl
          apply Or.inr
          exact assump_32
        case inr assump_42 =>
          cases assump_42
          case inl assump_45 =>
            apply Or.inl
            apply Or.inr
            exact assump_32
          case inr assump_46 =>
            cases assump_46
            case inl assump_49 =>
              apply Or.inl
              apply Or.inr
              exact assump_32
            case inr assump_50 =>
              apply Or.inl
              apply Or.inr
              exact assump_32


variable (p4 p3 p2 p6 p0 : Prop)
theorem file90_57744 : ((((((False ∧ True) ∧ (p0 → False)) → ((p4 → p3) ∧ (p6 → False))) → False) ∨ ((((False → False) ∧ (False → p0)) ∨ ((p2 → False) ∨ (p2 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_41 : (((False ∧ True) ∧ (p0 → False)) → ((p4 → p3) ∧ (p6 → False))) := by
      intro assump_7
      apply And.intro
      intro assump_8
      cases assump_7
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      intro assump_17
      cases assump_7
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
    let assump_6 := assump_2 assump_41
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_42 : (((False → False) ∧ (False → p0)) ∨ ((p2 → False) ∨ (p2 → False))) := by
      apply Or.inl
      apply And.intro
      intro assump_32
      apply False.elim assump_32
      intro assump_35
      apply False.elim assump_35
    let assump_31 := assump_3 assump_42
    apply False.elim assump_31


variable (p2 p7 p5 p0 p6 p3 p1 : Prop)
theorem file90_58946 : ((((((True ∧ True) ∧ (p7 ∧ p2)) → ((p3 ∧ p0) → (p1 ∨ p3))) ∨ (((p0 → False) → False) ∧ ((p5 → p6) → False))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((True ∧ True) ∧ (p7 ∧ p2)) → ((p3 ∧ p0) → (p1 ∨ p3))) ∨ (((p0 → False) → False) ∧ ((p5 → p6) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            apply Or.inr
            exact assump_7
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p7 p0 p5 p1 p4 p2 p3 : Prop)
theorem file90_59715 : ((((((p0 → False) ∧ (p0 → p3)) ∨ ((p2 → False) ∨ (p7 → False))) → (((p1 ∧ p0) ∧ (p5 → False)) ∨ ((p1 → p1) ∨ (p2 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p0 → False) ∧ (p0 → p3)) ∨ ((p2 → False) ∨ (p7 → False))) → (((p1 ∧ p0) ∧ (p5 → False)) ∨ ((p1 → p1) ∨ (p2 ∧ p4)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inr
        apply Or.inl
        intro assump_14
        exact assump_14
    case inr assump_7 =>
      cases assump_7
      case inl assump_17 =>
        apply Or.inr
        apply Or.inl
        intro assump_21
        exact assump_21
      case inr assump_18 =>
        apply Or.inr
        apply Or.inl
        intro assump_26
        exact assump_26
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p0 p4 p7 p2 p3 p5 p6 : Prop)
theorem file90_60645 : (((((p3 ∨ True) ∨ (p5 → p4)) → False) ∧ (((p5 → p7) → False) ∧ ((p4 → p4) → False))) → ((((p0 ∧ p3) ∨ (True → p4)) ∧ ((p0 → False) → False)) → (((False → p7) ∨ (p5 ∨ p0)) ∧ ((p2 → False) ∨ (p2 → p6))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            apply Or.inl
            intro assump_25
            apply False.elim assump_25
    case inr assump_6 =>
      cases assump_1
      case intro assump_32 assump_33 =>
        cases assump_33
        case intro assump_36 assump_37 =>
          apply Or.inl
          intro assump_42
          apply False.elim assump_42
  cases assump_2
  case intro assump_45 assump_46 =>
    cases assump_45
    case inl assump_47 =>
      cases assump_47
      case intro assump_49 assump_50 =>
        cases assump_1
        case intro assump_57 assump_58 =>
          cases assump_58
          case intro assump_61 assump_62 =>
            apply Or.inl
            intro assump_67
            have assump_103 : (p4 → p4) := by
              intro assump_72
              exact assump_72
            let assump_71 := assump_62 assump_103
            apply False.elim assump_71
    case inr assump_48 =>
      cases assump_1
      case intro assump_82 assump_83 =>
        cases assump_83
        case intro assump_86 assump_87 =>
          apply Or.inl
          intro assump_92
          have assump_104 : (p4 → p4) := by
            intro assump_97
            exact assump_97
          let assump_96 := assump_87 assump_104
          apply False.elim assump_96


variable (p7 p2 p3 p1 p4 p5 p0 p6 : Prop)
theorem file90_62522 : (((((True → False) ∨ (p5 → p6)) ∧ ((p6 → False) → (p0 → p3))) → (((p2 ∧ p1) → (p2 ∨ p0)) ∨ ((p5 ∨ p0) ∧ (p4 → False)))) ∨ ((((p7 ∧ p0) → (p1 ∨ p6)) → False) → (((p4 → p7) ∧ (True ∨ p7)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply Or.inl
        exact assump_11
    case inr assump_5 =>
      apply Or.inl
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        apply Or.inl
        exact assump_22


variable (p5 p6 p3 p4 : Prop)
theorem file90_63227 : ((((((p5 ∨ p5) → False) ∧ ((p3 ∨ p5) ∧ (True ∨ p3))) → (((False → False) → False) ∧ ((p3 ∧ False) → (p3 ∨ p3)))) ∧ ((((p4 → p5) → False) ∨ ((False → False) → False)) ∧ (((p4 → False) → (p4 → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_46 : ((p4 → False) → (p4 → p6)) := by
          intro assump_15
          intro assump_16
          have assump_47 : p4 := by
            exact assump_16
          let assump_21 := assump_15 assump_47
          apply False.elim assump_21
        let assump_14 := assump_7 assump_46
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_48 : ((p4 → False) → (p4 → p6)) := by
          intro assump_33
          intro assump_34
          have assump_49 : p4 := by
            exact assump_34
          let assump_39 := assump_33 assump_49
          apply False.elim assump_39
        let assump_32 := assump_7 assump_48
        apply False.elim assump_32


variable (p3 p6 p4 p1 p7 : Prop)
theorem file90_64378 : (((((p7 → p1) → (True ∨ p3)) → False) → False) ∨ ((((p3 ∨ p1) ∧ (False ∨ p6)) ∧ ((p1 ∨ p3) ∨ (p4 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p7 → p1) → (True ∨ p3)) := by
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p4 p7 p1 p5 p3 p2 : Prop)
theorem file90_64770 : ((((((p7 ∨ False) ∨ (p5 ∨ False)) ∨ ((p5 ∧ p2) → False)) → False) ∧ ((((p4 ∧ p7) ∨ (p3 ∧ p2)) ∧ ((p4 ∨ p1) ∨ (p6 ∨ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : (((p7 ∨ False) ∨ (p5 ∨ False)) ∨ ((p5 ∧ p2) → False)) := by
      apply Or.inr
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_28 : (((p7 ∨ False) ∨ (p5 ∨ False)) ∨ ((p5 ∧ p2) → False)) := by
          apply Or.inl
          apply Or.inr
          apply Or.inl
          exact assump_11
        let assump_20 := assump_2 assump_28
        apply False.elim assump_20
    let assump_9 := assump_2 assump_27
    apply False.elim assump_9


variable (p6 p7 p4 p1 p3 p0 : Prop)
theorem file90_65556 : (((((False → p3) → False) → False) ∨ (((p6 ∨ p7) ∧ (p0 → p1)) ∧ ((p7 ∧ p0) → (p4 → p6)))) ∨ ((((p1 → p3) ∧ (True → True)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → p3) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p3 p0 p5 p7 p4 : Prop)
theorem file90_65962 : ((((((p7 ∧ p3) ∨ (p5 ∨ p1)) ∨ ((p4 → False) → (p4 → p3))) ∨ (((p4 ∨ p0) → (p0 ∨ p5)) ∨ ((p4 → p7) ∨ (p0 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 ∧ p3) ∨ (p5 ∨ p1)) ∨ ((p4 → False) → (p4 → p3))) ∨ (((p4 ∨ p0) → (p0 ∨ p5)) ∨ ((p4 → p7) ∨ (p0 ∨ False)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    intro assump_6
    have assump_19 : p4 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p4 p2 p6 p3 : Prop)
theorem file90_66574 : ((((((True → False) ∧ (p6 → False)) ∨ ((p2 → True) → False)) → (((p6 → False) ∨ (p3 → False)) ∨ ((p0 → True) ∧ (p4 → p2)))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((True → False) ∧ (p6 → False)) ∨ ((p2 → True) → False)) → (((p6 → False) ∨ (p3 → False)) ∨ ((p0 → True) ∧ (p4 → p2)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        have assump_37 : p6 := by
          exact assump_14
        let assump_18 := assump_9 assump_37
        apply False.elim assump_18
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_24
      have assump_38 : (p2 → True) := by
        intro assump_29
        apply True.intro
      let assump_28 := assump_7 assump_38
      apply False.elim assump_28
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p3 p0 : Prop)
theorem file90_67576 : (((((True → False) ∧ (p3 ∧ p0)) → False) → False) → False) := by
  intro assump_1
  have assump_25 : (((True → False) ∧ (p3 ∧ p0)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p6 p2 p4 p3 p1 : Prop)
theorem file90_68124 : (((((p4 ∧ p6) ∧ (p4 → p2)) ∨ ((True → False) → (p0 ∧ p4))) ∨ (((p4 ∨ p0) → (p1 ∧ False)) ∨ ((True ∧ p0) ∨ (p6 ∨ p3)))) ∧ ((((True ∨ p2) → False) ∧ ((False → False) → False)) → False)) := by
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply And.intro
  have assump_28 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4
  have assump_29 : True := by
    apply True.intro
  let assump_10 := assump_1 assump_29
  apply False.elim assump_10
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    have assump_30 : (False → False) := by
      intro assump_22
      apply False.elim assump_22
    let assump_21 := assump_16 assump_30
    apply False.elim assump_21


variable (p1 p0 p7 p2 p5 : Prop)
theorem file90_68930 : ((((((False → False) → (p0 ∨ True)) ∨ ((p5 → False) ∧ (p5 ∧ False))) → (((p0 → False) ∧ (p1 → False)) → False)) ∧ ((((p7 ∧ False) ∨ (p0 → p5)) → False) ∧ (((p7 ∧ p2) → (p7 ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply Or.inl
          exact assump_14
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p6 p5 p3 p2 p4 : Prop)
theorem file90_69582 : (((((False → False) → False) → False) ∨ (((p2 ∧ p5) → False) → ((p4 → False) → (p5 ∨ True)))) ∨ ((((False → p4) ∨ (p6 → False)) ∨ ((p3 → False) ∨ (p5 → p5))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p3 : Prop)
theorem file90_70006 : (((((p3 ∧ p1) ∧ (p3 → False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : (((p3 ∧ p1) ∧ (p3 → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_24 : p3 := by
          exact assump_8
        let assump_16 := assump_7 assump_24
        apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p2 p3 p0 p6 p7 : Prop)
theorem file90_70544 : (((((p0 → True) → False) → False) ∧ (((p6 ∧ False) → (p2 ∧ p5)) ∨ ((p2 → False) → (False → False)))) ∨ ((((p5 → False) → False) ∧ ((p7 → p5) → (False → False))) ∧ (((p3 → p0) → False) ∧ ((p0 → p5) ∨ (p2 ∨ True))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_22 : (p0 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4
  apply Or.inl
  intro assump_9
  apply And.intro
  cases assump_9
  case intro assump_10 assump_11 =>
    apply False.elim assump_11
  cases assump_9
  case intro assump_16 assump_17 =>
    apply False.elim assump_17


variable (p6 p2 p7 p5 p0 p1 p3 : Prop)
theorem file90_71238 : ((((((p6 ∧ p0) ∨ (p3 ∧ p0)) ∨ ((p2 → p0) ∧ (p3 ∧ p3))) ∨ (((p1 ∨ p2) → (p5 ∧ p0)) ∧ ((True ∧ p3) ∨ (False ∨ p0)))) ∧ ((((True ∧ False) → False) → ((True → False) ∧ (p3 → p7))) ∧ (((p7 → True) ∧ (p2 ∨ p1)) → ((True ∧ p7) ∨ (p2 ∨ False))))) → False) := by
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
              have assump_155 : ((True ∧ False) → False) := by
                intro assump_25
                cases assump_25
                case intro assump_26 assump_27 =>
                  apply False.elim assump_27
              let assump_24 := assump_16 assump_155
              let assump_32 := And.left assump_24
              have assump_156 : True := by
                apply True.intro
              let assump_33 := assump_32 assump_156
              apply False.elim assump_33
        case inr assump_9 =>
          cases assump_9
          case intro assump_37 assump_38 =>
            cases assump_3
            case intro assump_43 assump_44 =>
              have assump_157 : ((True ∧ False) → False) := by
                intro assump_52
                cases assump_52
                case intro assump_53 assump_54 =>
                  apply False.elim assump_54
              let assump_51 := assump_43 assump_157
              let assump_59 := And.left assump_51
              have assump_158 : True := by
                apply True.intro
              let assump_60 := assump_59 assump_158
              apply False.elim assump_60
      case inr assump_7 =>
        cases assump_7
        case intro assump_64 assump_65 =>
          cases assump_65
          case intro assump_68 assump_69 =>
            cases assump_3
            case intro assump_74 assump_75 =>
              have assump_159 : ((True ∧ False) → False) := by
                intro assump_83
                cases assump_83
                case intro assump_84 assump_85 =>
                  apply False.elim assump_85
              let assump_82 := assump_74 assump_159
              let assump_90 := And.left assump_82
              have assump_160 : True := by
                apply True.intro
              let assump_91 := assump_90 assump_160
              apply False.elim assump_91
    case inr assump_5 =>
      cases assump_5
      case intro assump_95 assump_96 =>
        cases assump_96
        case inl assump_99 =>
          cases assump_99
          case intro assump_101 assump_102 =>
            cases assump_3
            case intro assump_107 assump_108 =>
              have assump_161 : ((True ∧ False) → False) := by
                intro assump_116
                cases assump_116
                case intro assump_117 assump_118 =>
                  apply False.elim assump_118
              let assump_115 := assump_107 assump_161
              let assump_123 := And.left assump_115
              have assump_162 : True := by
                apply True.intro
              let assump_124 := assump_123 assump_162
              apply False.elim assump_124
        case inr assump_100 =>
          cases assump_100
          case inl assump_128 =>
            apply False.elim assump_128
          case inr assump_129 =>
            cases assump_3
            case intro assump_134 assump_135 =>
              have assump_163 : ((True ∧ False) → False) := by
                intro assump_143
                cases assump_143
                case intro assump_144 assump_145 =>
                  apply False.elim assump_145
              let assump_142 := assump_134 assump_163
              let assump_150 := And.left assump_142
              have assump_164 : True := by
                apply True.intro
              let assump_151 := assump_150 assump_164
              apply False.elim assump_151


variable (p0 p6 p5 p4 p7 p3 : Prop)
theorem file90_75327 : ((((((False → False) → False) → False) ∧ (((True → True) ∨ (p0 → False)) → ((p7 → p0) → False))) ∧ ((((True → p5) ∧ (p3 ∨ p4)) ∧ ((p0 ∨ p5) → (True ∧ False))) ∧ (((p5 ∧ p7) ∧ (p6 ∨ p6)) ∧ ((True ∧ p4) → False)))) → False) := by
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
            cases assump_15
            case inl assump_18 =>
              cases assump_11
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_27
                    case inl assump_34 =>
                      have assump_96 : (p0 ∨ p5) := by
                        apply Or.inr
                        exact assump_28
                      let assump_44 := assump_13 assump_96
                      let assump_45 := And.right assump_44
                      apply False.elim assump_45
                    case inr assump_35 =>
                      have assump_97 : (p0 ∨ p5) := by
                        apply Or.inr
                        exact assump_28
                      let assump_58 := assump_13 assump_97
                      let assump_59 := And.right assump_58
                      apply False.elim assump_59
            case inr assump_19 =>
              cases assump_11
              case intro assump_68 assump_69 =>
                cases assump_68
                case intro assump_70 assump_71 =>
                  cases assump_70
                  case intro assump_72 assump_73 =>
                    cases assump_71
                    case inl assump_78 =>
                      have assump_98 : (True ∧ p4) := by
                        apply And.intro
                        apply True.intro
                        exact assump_19
                      let assump_84 := assump_69 assump_98
                      apply False.elim assump_84
                    case inr assump_79 =>
                      have assump_99 : (True ∧ p4) := by
                        apply And.intro
                        apply True.intro
                        exact assump_19
                      let assump_92 := assump_69 assump_99
                      apply False.elim assump_92


variable (p7 p4 p6 p3 p2 p5 p1 : Prop)
theorem file90_77936 : (((((True ∨ p4) → False) → False) ∨ (((True ∨ p5) → (p7 ∧ p4)) → False)) ∨ ((((p5 → False) ∧ (p4 ∧ p7)) → ((p1 ∨ True) → (p2 → False))) ∧ (((p6 → False) → (p1 ∨ p6)) → ((p4 → False) ∧ (p3 ∨ True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_11
  have assump_18 : (True ∨ p4) := by
    apply Or.inl
    apply True.intro
  let assump_14 := assump_11 assump_18
  apply False.elim assump_14


variable (p5 p4 p6 p2 p3 p0 p7 : Prop)
theorem file90_78396 : ((((((p0 ∨ p5) ∧ (p7 ∨ p3)) ∨ ((p5 ∧ p3) → (p6 ∧ p2))) ∨ (((True ∧ p2) ∨ (p5 → p4)) → ((p2 ∧ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p0 ∨ p5) ∧ (p7 ∨ p3)) ∨ ((p5 ∧ p3) → (p6 ∧ p2))) ∨ (((True ∧ p2) ∨ (p5 → p4)) → ((p2 ∧ p5) → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_34 : ((((p0 ∨ p5) ∧ (p7 ∨ p3)) ∨ ((p5 ∧ p3) → (p6 ∧ p2))) ∨ (((True ∧ p2) ∨ (p5 → p4)) → ((p2 ∧ p5) → False))) := by
        apply Or.inl
        apply Or.inl
        apply And.intro
        apply Or.inr
        exact assump_6
        apply Or.inr
        exact assump_7
      let assump_14 := assump_1 assump_34
      apply False.elim assump_14
    cases assump_5
    case intro assump_18 assump_19 =>
      have assump_35 : ((((p0 ∨ p5) ∧ (p7 ∨ p3)) ∨ ((p5 ∧ p3) → (p6 ∧ p2))) ∨ (((True ∧ p2) ∨ (p5 → p4)) → ((p2 ∧ p5) → False))) := by
        apply Or.inl
        apply Or.inl
        apply And.intro
        apply Or.inr
        exact assump_18
        apply Or.inr
        exact assump_19
      let assump_26 := assump_1 assump_35
      apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p7 p5 p1 p2 p6 : Prop)
theorem file90_79713 : (((((p2 → False) ∧ (p5 ∧ p2)) → ((p5 → False) ∧ (p5 ∧ False))) ∨ (((p6 ∧ p5) → False) ∧ ((p6 → p6) ∧ (p2 → False)))) ∨ ((((p1 → p1) → (p7 → False)) → False) → (((p7 ∧ False) → False) ∧ ((p6 ∨ p7) ∧ (p7 ∨ p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_47 : p2 := by
        exact assump_10
      let assump_17 := assump_5 assump_47
      apply False.elim assump_17
  apply And.intro
  cases assump_1
  case intro assump_21 assump_22 =>
    cases assump_22
    case intro assump_25 assump_26 =>
      exact assump_25
  cases assump_1
  case intro assump_31 assump_32 =>
    cases assump_32
    case intro assump_35 assump_36 =>
      have assump_48 : p2 := by
        exact assump_36
      let assump_43 := assump_31 assump_48
      apply False.elim assump_43


variable (p2 p7 p0 p6 p1 p3 : Prop)
theorem file90_80705 : ((((((p3 ∨ p6) ∧ (p2 → False)) ∨ ((p3 ∧ p0) ∧ (True ∧ p1))) ∨ (((p3 ∨ True) ∧ (p7 → p7)) → ((False ∧ p6) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p3 ∨ p6) ∧ (p2 → False)) ∨ ((p3 ∧ p0) ∧ (True ∧ p1))) ∨ (((p3 ∨ True) ∧ (p7 → p7)) → ((False ∧ p6) → (p0 → False)))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p5 p1 p4 p7 p6 : Prop)
theorem file90_81304 : ((((((p1 → False) → False) → ((p5 ∧ p4) → (p4 → True))) ∨ (((True → False) → False) → ((p3 ∨ p6) ∧ (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p1 → False) → False) → ((p5 ∧ p4) → (p4 → True))) ∨ (((True → False) → False) → ((p3 ∨ p6) ∧ (p7 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p0 p2 p5 p3 : Prop)
theorem file90_81815 : (((((p0 → True) → False) ∧ ((p3 → False) ∨ (p5 → p6))) ∧ (((p2 → True) ∧ (True ∧ p2)) → False)) → False) := by
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_33
      case inl assump_36 =>
        have assump_62 : (p0 → True) := by
          intro assump_46
          apply True.intro
        let assump_45 := assump_32 assump_62
        apply False.elim assump_45
      case inr assump_37 =>
        have assump_63 : (p0 → True) := by
          intro assump_58
          apply True.intro
        let assump_57 := assump_32 assump_63
        apply False.elim assump_57


variable (p5 p7 p4 p0 p2 p1 p3 : Prop)
theorem file90_82549 : ((((((p0 → False) → False) → ((p5 ∨ True) ∧ (p5 → False))) ∧ (((p1 ∧ p3) ∧ (False ∧ p4)) ∧ ((p0 → True) ∧ (True ∧ p7)))) ∧ ((((p3 → p3) ∧ (True → False)) → False) ∨ (((False ∧ p7) ∨ (False → p7)) ∧ ((p2 ∧ p0) → (p7 ∧ p2))))) → False) := by
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
            cases assump_11
            case intro assump_18 assump_19 =>
              apply False.elim assump_18


variable (p4 p1 p0 p5 p6 p2 p3 p7 : Prop)
theorem file90_83287 : (((((p1 ∨ p3) ∧ (p5 ∧ False)) ∧ ((p7 ∨ p0) → (p3 → True))) ∧ (((p0 ∨ p5) → (False ∨ p2)) → ((p4 → False) → (p6 → p2)))) ∨ ((((False → False) ∧ (p4 ∧ p2)) ∧ ((True → p3) ∧ (p4 → False))) → (((p5 ∧ p5) ∧ (p5 → False)) → ((False → False) ∨ (True ∨ p0))))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_14
            case intro assump_25 assump_26 =>
              apply Or.inl
              intro assump_31
              apply False.elim assump_31


variable (p1 p4 p5 p2 p0 : Prop)
theorem file90_84127 : (((((p2 ∨ True) ∨ (p0 ∨ p2)) ∨ ((p1 → p5) → False)) → False) → ((((p5 → False) → False) ∨ ((p4 → p4) → False)) → False)) := by
  intro assump_23
  intro assump_24
  cases assump_24
  case inl assump_25 =>
    have assump_43 : (((p2 ∨ True) ∨ (p0 ∨ p2)) ∨ ((p1 → p5) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_31 := assump_23 assump_43
    apply False.elim assump_31
  case inr assump_26 =>
    have assump_44 : (((p2 ∨ True) ∨ (p0 ∨ p2)) ∨ ((p1 → p5) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_39 := assump_23 assump_44
    apply False.elim assump_39


variable (p3 p7 p4 p5 p2 p6 p1 p0 : Prop)
theorem file90_84880 : (((((p1 ∨ p0) → False) → ((True → False) → False)) ∨ (((p3 ∨ False) → (True → p4)) ∧ ((p1 → p1) ∨ (True → p1)))) ∨ ((((p2 → p7) → False) → ((False → True) ∨ (p2 → False))) → (((p2 → False) ∧ (p5 → p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_12 : True := by
    apply True.intro
  let assump_8 := assump_2 assump_12
  apply False.elim assump_8


variable (p0 p2 p3 p4 p1 p6 p5 : Prop)
theorem file90_85342 : (((((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) → False) → ((((p1 → False) → (p3 ∧ p6)) ∨ ((p4 → p1) → (p2 → False))) → (((p0 ∨ p4) ∨ (p6 ∨ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case inl assump_10 =>
        have assump_114 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_17
          apply Or.inl
          apply True.intro
        let assump_16 := assump_1 assump_114
        apply False.elim assump_16
      case inr assump_11 =>
        have assump_115 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_28
          apply Or.inl
          apply True.intro
        let assump_27 := assump_1 assump_115
        apply False.elim assump_27
    case inr assump_7 =>
      cases assump_2
      case inl assump_36 =>
        have assump_116 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_43
          apply Or.inl
          apply True.intro
        let assump_42 := assump_1 assump_116
        apply False.elim assump_42
      case inr assump_37 =>
        have assump_117 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_54
          apply Or.inl
          apply True.intro
        let assump_53 := assump_1 assump_117
        apply False.elim assump_53
  case inr assump_5 =>
    cases assump_5
    case inl assump_60 =>
      cases assump_2
      case inl assump_64 =>
        have assump_118 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_71
          apply Or.inl
          apply True.intro
        let assump_70 := assump_1 assump_118
        apply False.elim assump_70
      case inr assump_65 =>
        have assump_119 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_82
          apply Or.inl
          apply True.intro
        let assump_81 := assump_1 assump_119
        apply False.elim assump_81
    case inr assump_61 =>
      cases assump_2
      case inl assump_90 =>
        have assump_120 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_97
          apply Or.inl
          apply True.intro
        let assump_96 := assump_1 assump_120
        apply False.elim assump_96
      case inr assump_91 =>
        have assump_121 : (((p1 → p5) → (True ∨ False)) ∨ ((p2 → p4) ∧ (p0 ∨ p4))) := by
          apply Or.inl
          intro assump_108
          apply Or.inl
          apply True.intro
        let assump_107 := assump_1 assump_121
        apply False.elim assump_107


variable (p3 p0 p6 p7 p2 : Prop)
theorem file90_88281 : ((((((p3 → False) ∨ (True → False)) → False) ∧ (((True ∨ p6) ∨ (p7 ∧ p3)) → False)) ∨ ((((False ∨ p2) ∧ (p0 → p2)) → False) ∧ (((p7 ∧ p0) ∨ (p0 → p6)) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_48 : ((True ∨ p6) ∨ (p7 ∧ p3)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_10 := assump_5 assump_48
      apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            have assump_49 : (False → False) := by
              intro assump_31
              apply False.elim assump_31
            let assump_30 := assump_19 assump_49
            apply False.elim assump_30
        case inr assump_21 =>
          have assump_50 : (False → False) := by
            intro assump_42
            apply False.elim assump_42
          let assump_41 := assump_19 assump_50
          apply False.elim assump_41


variable (p4 p2 p0 p7 p1 : Prop)
theorem file90_89550 : ((((((p2 → True) → False) ∨ ((p4 ∨ p2) → False)) → (((True → False) → False) ∨ ((p7 ∨ p1) → (p0 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p2 → True) → False) ∨ ((p4 ∨ p2) → False)) → (((True → False) → False) ∨ ((p7 ∨ p1) → (p0 ∨ p7)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      have assump_30 : True := by
        apply True.intro
      let assump_13 := assump_10 assump_30
      apply False.elim assump_13
    case inr assump_7 =>
      apply Or.inl
      intro assump_19
      have assump_31 : True := by
        apply True.intro
      let assump_22 := assump_19 assump_31
      apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p0 p6 p5 p7 : Prop)
theorem file90_90386 : (((((p6 → p7) → False) → ((False ∧ p6) → False)) ∨ (((True → p7) → (p7 → False)) → False)) ∨ ((((p5 ∨ p0) → False) → False) ∨ (((p7 ∨ True) → (p1 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p5 p1 p3 : Prop)
theorem file90_90755 : ((((((p1 ∧ p3) ∨ (p5 → p5)) → False) → False) → False) → False) := by
  intro assump_14
  have assump_31 : ((((p1 ∧ p3) ∨ (p5 → p5)) → False) → False) := by
    intro assump_18
    have assump_32 : ((p1 ∧ p3) ∨ (p5 → p5)) := by
      apply Or.inr
      intro assump_22
      exact assump_22
    let assump_21 := assump_18 assump_32
    apply False.elim assump_21
  let assump_17 := assump_14 assump_31
  apply False.elim assump_17


variable (p6 p0 p7 p3 p4 : Prop)
theorem file90_91243 : ((((((p7 ∧ p6) ∨ (p3 → False)) → False) → False) ∧ ((((True ∨ p6) → False) → ((p3 ∨ p7) ∨ (p0 → p4))) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    have assump_33 : (((True ∨ p6) → False) → ((p3 ∨ p7) ∨ (p0 → p4))) := by
      intro assump_19
      apply Or.inr
      intro assump_22
      have assump_34 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_26 := assump_19 assump_34
      apply False.elim assump_26
    let assump_18 := assump_13 assump_33
    apply False.elim assump_18


variable (p5 p1 p0 p7 p3 p6 : Prop)
theorem file90_91877 : ((((((p7 ∧ p7) ∨ (p3 ∨ True)) ∧ ((p5 ∧ p5) → False)) → (((p0 → False) → (p5 → False)) ∨ ((p6 ∨ p5) → (p1 ∨ True)))) → False) → False) := by
  intro assump_29
  have assump_95 : ((((p7 ∧ p7) ∨ (p3 ∨ True)) ∧ ((p5 ∧ p5) → False)) → (((p0 → False) → (p5 → False)) ∨ ((p6 ∨ p5) → (p1 ∨ True)))) := by
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      cases assump_34
      case inl assump_36 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          apply Or.inl
          intro assump_46
          intro assump_47
          have assump_96 : (p5 ∧ p5) := by
            apply And.intro
            exact assump_47
            exact assump_47
          let assump_54 := assump_35 assump_96
          apply False.elim assump_54
      case inr assump_37 =>
        cases assump_37
        case inl assump_58 =>
          apply Or.inl
          intro assump_64
          intro assump_65
          have assump_97 : (p5 ∧ p5) := by
            apply And.intro
            exact assump_65
            exact assump_65
          let assump_72 := assump_35 assump_97
          apply False.elim assump_72
        case inr assump_59 =>
          apply Or.inl
          intro assump_80
          intro assump_81
          have assump_98 : (p5 ∧ p5) := by
            apply And.intro
            exact assump_81
            exact assump_81
          let assump_88 := assump_35 assump_98
          apply False.elim assump_88
  let assump_32 := assump_29 assump_95
  apply False.elim assump_32


variable (p3 p6 p4 p2 p1 : Prop)
theorem file90_93463 : ((((((True ∨ p2) → False) ∧ ((p1 ∧ p3) → False)) → (((p4 → False) → False) → False)) ∧ ((((p6 ∧ p4) ∨ (p2 ∨ False)) ∨ ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p6 ∧ p4) ∨ (p2 ∨ False)) ∨ ((True → False) → False)) := by
      apply Or.inr
      intro assump_9
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p5 p1 : Prop)
theorem file90_94077 : (((((p6 ∨ p5) ∧ (p1 ∧ p5)) → ((p6 ∧ p6) ∧ (p5 → False))) → (((True → False) → False) ∧ ((True → False) → (False → p1)))) ∧ ((((True → False) → False) → False) → False)) := by
  apply And.intro
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_30 : True := by
    apply True.intro
  let assump_8 := assump_2 assump_30
  apply False.elim assump_8
  intro assump_12
  intro assump_13
  apply False.elim assump_13
  intro assump_16
  have assump_31 : ((True → False) → False) := by
    intro assump_20
    have assump_32 : True := by
      apply True.intro
    let assump_23 := assump_20 assump_32
    apply False.elim assump_23
  let assump_19 := assump_16 assump_31
  apply False.elim assump_19


variable (p1 p2 p6 p5 p0 : Prop)
theorem file90_94843 : ((((((p5 → False) ∧ (p0 ∨ True)) ∧ ((p2 ∨ p0) → False)) → (((p6 → False) → False) → ((p2 ∧ p2) → (p1 → p5)))) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p5 → False) ∧ (p0 ∨ True)) ∧ ((p2 ∨ p0) → False)) → (((p6 → False) → False) → ((p2 ∧ p2) → (p1 → p5)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_5
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_22
          case inl assump_25 =>
            have assump_47 : (p2 ∨ p0) := by
              apply Or.inl
              exact assump_12
            let assump_31 := assump_20 assump_47
            apply False.elim assump_31
          case inr assump_26 =>
            have assump_48 : (p2 ∨ p0) := by
              apply Or.inl
              exact assump_12
            let assump_39 := assump_20 assump_48
            apply False.elim assump_39
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p4 p5 p0 p6 p1 p3 p7 : Prop)
theorem file90_95985 : (((((p7 ∧ p1) → (p4 → p1)) ∨ ((p7 → False) ∨ (p5 ∨ False))) → (((False ∨ p3) → False) ∨ ((p5 → False) ∧ (p0 ∧ False)))) → ((((p6 → True) ∧ (False ∧ True)) ∧ ((p1 → False) ∨ (p6 → p6))) → (((p4 → False) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        apply False.elim assump_12


variable (p4 p2 p7 p5 p1 p6 : Prop)
theorem file90_96526 : ((((((False ∧ False) → (p1 → False)) → ((True ∨ p1) ∨ (p2 → False))) → False) ∨ ((((p2 ∨ p6) ∨ (p2 ∨ p5)) ∨ ((p4 ∧ p2) → (True → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_35 : (((False ∧ False) → (p1 → False)) → ((True ∨ p1) ∨ (p2 → False))) := by
      intro assump_7
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_6 := assump_2 assump_35
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_36 : (((p2 ∨ p6) ∨ (p2 ∨ p5)) ∨ ((p4 ∧ p2) → (True → p7))) := by
      apply Or.inr
      intro assump_16
      intro assump_17
      cases assump_16
      case intro assump_20 assump_21 =>
        have assump_37 : (((p2 ∨ p6) ∨ (p2 ∨ p5)) ∨ ((p4 ∧ p2) → (True → p7))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_21
        let assump_28 := assump_3 assump_37
        apply False.elim assump_28
    let assump_15 := assump_3 assump_36
    apply False.elim assump_15


variable (p3 p4 p6 p5 p2 p0 p7 p1 : Prop)
theorem file90_97612 : (((((p0 ∨ p0) ∧ (p6 ∨ p3)) ∧ ((False ∧ p1) ∧ (p6 ∨ p2))) ∧ (((p5 ∨ p4) ∧ (p2 → p5)) → ((p7 → False) ∨ (p1 ∧ p3)))) → ((((p7 → False) → (p2 ∧ p4)) ∧ ((p6 ∨ p1) → (p5 ∨ True))) ∧ (((p1 → False) → (p7 → p0)) ∧ ((p0 → False) ∧ (p7 → p4))))) := by
  intro assump_4
  apply And.intro
  apply And.intro
  intro assump_5
  apply And.intro
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_13
          case inl assump_18 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
          case inr assump_19 =>
            cases assump_11
            case intro assump_30 assump_31 =>
              cases assump_30
              case intro assump_32 assump_33 =>
                apply False.elim assump_32
        case inr assump_15 =>
          cases assump_13
          case inl assump_38 =>
            cases assump_11
            case intro assump_42 assump_43 =>
              cases assump_42
              case intro assump_44 assump_45 =>
                apply False.elim assump_44
          case inr assump_39 =>
            cases assump_11
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                apply False.elim assump_52
  cases assump_4
  case intro assump_58 assump_59 =>
    cases assump_58
    case intro assump_60 assump_61 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        cases assump_62
        case inl assump_64 =>
          cases assump_63
          case inl assump_68 =>
            cases assump_61
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                apply False.elim assump_74
          case inr assump_69 =>
            cases assump_61
            case intro assump_80 assump_81 =>
              cases assump_80
              case intro assump_82 assump_83 =>
                apply False.elim assump_82
        case inr assump_65 =>
          cases assump_63
          case inl assump_88 =>
            cases assump_61
            case intro assump_92 assump_93 =>
              cases assump_92
              case intro assump_94 assump_95 =>
                apply False.elim assump_94
          case inr assump_89 =>
            cases assump_61
            case intro assump_100 assump_101 =>
              cases assump_100
              case intro assump_102 assump_103 =>
                apply False.elim assump_102
  intro assump_106
  cases assump_106
  case inl assump_107 =>
    cases assump_4
    case intro assump_111 assump_112 =>
      cases assump_111
      case intro assump_113 assump_114 =>
        cases assump_113
        case intro assump_115 assump_116 =>
          cases assump_115
          case inl assump_117 =>
            cases assump_116
            case inl assump_121 =>
              cases assump_114
              case intro assump_125 assump_126 =>
                cases assump_125
                case intro assump_127 assump_128 =>
                  apply False.elim assump_127
            case inr assump_122 =>
              cases assump_114
              case intro assump_133 assump_134 =>
                cases assump_133
                case intro assump_135 assump_136 =>
                  apply False.elim assump_135
          case inr assump_118 =>
            cases assump_116
            case inl assump_141 =>
              cases assump_114
              case intro assump_145 assump_146 =>
                cases assump_145
                case intro assump_147 assump_148 =>
                  apply False.elim assump_147
            case inr assump_142 =>
              cases assump_114
              case intro assump_153 assump_154 =>
                cases assump_153
                case intro assump_155 assump_156 =>
                  apply False.elim assump_155
  case inr assump_108 =>
    cases assump_4
    case intro assump_161 assump_162 =>
      cases assump_161
      case intro assump_163 assump_164 =>
        cases assump_163
        case intro assump_165 assump_166 =>
          cases assump_165
          case inl assump_167 =>
            cases assump_166
            case inl assump_171 =>
              cases assump_164
              case intro assump_175 assump_176 =>
                cases assump_175
                case intro assump_177 assump_178 =>
                  apply False.elim assump_177
            case inr assump_172 =>
              cases assump_164
              case intro assump_183 assump_184 =>
                cases assump_183
                case intro assump_185 assump_186 =>
                  apply False.elim assump_185
          case inr assump_168 =>
            cases assump_166
            case inl assump_191 =>
              cases assump_164
              case intro assump_195 assump_196 =>
                cases assump_195
                case intro assump_197 assump_198 =>
                  apply False.elim assump_197
            case inr assump_192 =>
              cases assump_164
              case intro assump_203 assump_204 =>
                cases assump_203
                case intro assump_205 assump_206 =>
                  apply False.elim assump_205
  apply And.intro
  intro assump_209
  intro assump_210
  cases assump_4
  case intro assump_215 assump_216 =>
    cases assump_215
    case intro assump_217 assump_218 =>
      cases assump_217
      case intro assump_219 assump_220 =>
        cases assump_219
        case inl assump_221 =>
          cases assump_220
          case inl assump_225 =>
            cases assump_218
            case intro assump_229 assump_230 =>
              cases assump_229
              case intro assump_231 assump_232 =>
                apply False.elim assump_231
          case inr assump_226 =>
            cases assump_218
            case intro assump_237 assump_238 =>
              cases assump_237
              case intro assump_239 assump_240 =>
                apply False.elim assump_239
        case inr assump_222 =>
          cases assump_220
          case inl assump_245 =>
            cases assump_218
            case intro assump_249 assump_250 =>
              cases assump_249
              case intro assump_251 assump_252 =>
                apply False.elim assump_251
          case inr assump_246 =>
            cases assump_218
            case intro assump_257 assump_258 =>
              cases assump_257
              case intro assump_259 assump_260 =>
                apply False.elim assump_259
  apply And.intro
  intro assump_263
  cases assump_4
  case intro assump_266 assump_267 =>
    cases assump_266
    case intro assump_268 assump_269 =>
      cases assump_268
      case intro assump_270 assump_271 =>
        cases assump_270
        case inl assump_272 =>
          cases assump_271
          case inl assump_276 =>
            cases assump_269
            case intro assump_280 assump_281 =>
              cases assump_280
              case intro assump_282 assump_283 =>
                apply False.elim assump_282
          case inr assump_277 =>
            cases assump_269
            case intro assump_288 assump_289 =>
              cases assump_288
              case intro assump_290 assump_291 =>
                apply False.elim assump_290
        case inr assump_273 =>
          cases assump_271
          case inl assump_296 =>
            cases assump_269
            case intro assump_300 assump_301 =>
              cases assump_300
              case intro assump_302 assump_303 =>
                apply False.elim assump_302
          case inr assump_297 =>
            cases assump_269
            case intro assump_308 assump_309 =>
              cases assump_308
              case intro assump_310 assump_311 =>
                apply False.elim assump_310
  intro assump_314
  cases assump_4
  case intro assump_317 assump_318 =>
    cases assump_317
    case intro assump_319 assump_320 =>
      cases assump_319
      case intro assump_321 assump_322 =>
        cases assump_321
        case inl assump_323 =>
          cases assump_322
          case inl assump_327 =>
            cases assump_320
            case intro assump_331 assump_332 =>
              cases assump_331
              case intro assump_333 assump_334 =>
                apply False.elim assump_333
          case inr assump_328 =>
            cases assump_320
            case intro assump_339 assump_340 =>
              cases assump_339
              case intro assump_341 assump_342 =>
                apply False.elim assump_341
        case inr assump_324 =>
          cases assump_322
          case inl assump_347 =>
            cases assump_320
            case intro assump_351 assump_352 =>
              cases assump_351
              case intro assump_353 assump_354 =>
                apply False.elim assump_353
          case inr assump_348 =>
            cases assump_320
            case intro assump_359 assump_360 =>
              cases assump_359
              case intro assump_361 assump_362 =>
                apply False.elim assump_361


variable (p5 p0 p3 p4 p6 p2 p1 p7 : Prop)
theorem file90_107096 : (((((True → p5) ∨ (p4 → False)) ∨ ((p4 ∨ p3) ∨ (p4 → False))) → (((p6 ∨ p2) → False) → ((p1 → p1) ∧ (p2 → p1)))) ∨ ((((p2 ∨ p1) → (p7 → False)) → ((p6 → p2) → False)) ∧ (((p4 → False) ∧ (p3 ∨ p0)) → ((p5 → p3) → (p7 → p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case inl assump_10 =>
      exact assump_3
    case inr assump_11 =>
      exact assump_3
  case inr assump_9 =>
    cases assump_9
    case inl assump_16 =>
      cases assump_16
      case inl assump_18 =>
        exact assump_3
      case inr assump_19 =>
        exact assump_3
    case inr assump_17 =>
      exact assump_3
  intro assump_26
  cases assump_1
  case inl assump_31 =>
    cases assump_31
    case inl assump_33 =>
      have assump_75 : (p6 ∨ p2) := by
        apply Or.inr
        exact assump_26
      let assump_39 := assump_2 assump_75
      apply False.elim assump_39
    case inr assump_34 =>
      have assump_76 : (p6 ∨ p2) := by
        apply Or.inr
        exact assump_26
      let assump_46 := assump_2 assump_76
      apply False.elim assump_46
  case inr assump_32 =>
    cases assump_32
    case inl assump_50 =>
      cases assump_50
      case inl assump_52 =>
        have assump_77 : (p6 ∨ p2) := by
          apply Or.inr
          exact assump_26
        let assump_57 := assump_2 assump_77
        apply False.elim assump_57
      case inr assump_53 =>
        have assump_78 : (p6 ∨ p2) := by
          apply Or.inr
          exact assump_26
        let assump_64 := assump_2 assump_78
        apply False.elim assump_64
    case inr assump_51 =>
      have assump_79 : (p6 ∨ p2) := by
        apply Or.inr
        exact assump_26
      let assump_71 := assump_2 assump_79
      apply False.elim assump_71


variable (p4 p1 p5 p7 p3 p2 p0 : Prop)
theorem file90_108987 : ((((((p4 ∨ p0) ∧ (p7 ∧ p0)) → ((p3 ∧ p0) ∨ (p2 → False))) ∧ (((False ∨ p2) ∨ (p7 ∧ p4)) → ((True ∨ True) → (False ∨ p7)))) ∧ ((((p2 → p0) → False) ∧ ((p4 → p4) → False)) ∧ (((p0 ∨ p7) ∨ (p5 ∨ p7)) ∨ ((p1 → False) ∨ (False ∨ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case inl assump_18 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_20
              case inl assump_22 =>
                have assump_92 : (p4 → p4) := by
                  intro assump_28
                  exact assump_28
                let assump_27 := assump_13 assump_92
                apply False.elim assump_27
              case inr assump_23 =>
                have assump_93 : (p4 → p4) := by
                  intro assump_38
                  exact assump_38
                let assump_37 := assump_13 assump_93
                apply False.elim assump_37
            case inr assump_21 =>
              cases assump_21
              case inl assump_44 =>
                have assump_94 : (p4 → p4) := by
                  intro assump_50
                  exact assump_50
                let assump_49 := assump_13 assump_94
                apply False.elim assump_49
              case inr assump_45 =>
                have assump_95 : (p4 → p4) := by
                  intro assump_60
                  exact assump_60
                let assump_59 := assump_13 assump_95
                apply False.elim assump_59
          case inr assump_19 =>
            cases assump_19
            case inl assump_66 =>
              have assump_96 : (p4 → p4) := by
                intro assump_72
                exact assump_72
              let assump_71 := assump_13 assump_96
              apply False.elim assump_71
            case inr assump_67 =>
              cases assump_67
              case inl assump_78 =>
                apply False.elim assump_78
              case inr assump_79 =>
                have assump_97 : (p4 → p4) := by
                  intro assump_86
                  exact assump_86
                let assump_85 := assump_13 assump_97
                apply False.elim assump_85


variable (p7 p4 p5 p3 p1 : Prop)
theorem file90_111440 : (((((False → False) ∨ (p7 → False)) → False) → False) ∨ ((((p5 → False) ∨ (p5 → False)) → ((p1 ∧ p4) → False)) → (((p4 → False) → (p3 ∨ True)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (p7 → False)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p6 p4 p3 p7 p1 p2 p5 : Prop)
theorem file90_111887 : (((((p4 ∧ False) ∧ (False → p4)) ∨ ((True ∨ p0) → (p5 ∧ p3))) → (((p6 → False) ∧ (False ∧ p2)) → False)) ∨ ((((p6 ∧ p1) → False) ∨ ((p6 → True) ∧ (p4 → False))) ∧ (((p0 → p7) ∧ (True ∧ True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p6 p5 p0 p3 p4 : Prop)
theorem file90_112340 : ((((((p4 → False) → False) → ((p0 ∨ p5) → False)) ∨ (((p0 ∨ p0) → False) ∨ ((p3 ∧ p6) → False))) ∧ ((((p6 → False) → False) ∧ ((p4 → p6) ∧ (p3 ∨ p4))) ∧ (((p3 ∧ False) ∨ (p6 ∨ p0)) → False))) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case inl assump_27 =>
      cases assump_26
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          cases assump_34
          case intro assump_37 assump_38 =>
            cases assump_38
            case inl assump_41 =>
              have assump_190 : (p6 → False) := by
                intro assump_51
                have assump_191 : ((p3 ∧ False) ∨ (p6 ∨ p0)) := by
                  apply Or.inr
                  apply Or.inl
                  exact assump_51
                let assump_55 := assump_32 assump_191
                apply False.elim assump_55
              let assump_50 := assump_33 assump_190
              apply False.elim assump_50
            case inr assump_42 =>
              have assump_192 : (p6 → False) := by
                intro assump_71
                have assump_193 : ((p3 ∧ False) ∨ (p6 ∨ p0)) := by
                  apply Or.inr
                  apply Or.inl
                  exact assump_71
                let assump_75 := assump_32 assump_193
                apply False.elim assump_75
              let assump_70 := assump_33 assump_192
              apply False.elim assump_70
    case inr assump_28 =>
      cases assump_28
      case inl assump_82 =>
        cases assump_26
        case intro assump_86 assump_87 =>
          cases assump_86
          case intro assump_88 assump_89 =>
            cases assump_89
            case intro assump_92 assump_93 =>
              cases assump_93
              case inl assump_96 =>
                have assump_194 : (p6 → False) := by
                  intro assump_106
                  have assump_195 : ((p3 ∧ False) ∨ (p6 ∨ p0)) := by
                    apply Or.inr
                    apply Or.inl
                    exact assump_106
                  let assump_110 := assump_87 assump_195
                  apply False.elim assump_110
                let assump_105 := assump_88 assump_194
                apply False.elim assump_105
              case inr assump_97 =>
                have assump_196 : (p6 → False) := by
                  intro assump_126
                  have assump_197 : ((p3 ∧ False) ∨ (p6 ∨ p0)) := by
                    apply Or.inr
                    apply Or.inl
                    exact assump_126
                  let assump_130 := assump_87 assump_197
                  apply False.elim assump_130
                let assump_125 := assump_88 assump_196
                apply False.elim assump_125
      case inr assump_83 =>
        cases assump_26
        case intro assump_139 assump_140 =>
          cases assump_139
          case intro assump_141 assump_142 =>
            cases assump_142
            case intro assump_145 assump_146 =>
              cases assump_146
              case inl assump_149 =>
                have assump_198 : (p6 → False) := by
                  intro assump_159
                  have assump_199 : ((p3 ∧ False) ∨ (p6 ∨ p0)) := by
                    apply Or.inr
                    apply Or.inl
                    exact assump_159
                  let assump_163 := assump_140 assump_199
                  apply False.elim assump_163
                let assump_158 := assump_141 assump_198
                apply False.elim assump_158
              case inr assump_150 =>
                have assump_200 : (p6 → False) := by
                  intro assump_179
                  have assump_201 : ((p3 ∧ False) ∨ (p6 ∨ p0)) := by
                    apply Or.inr
                    apply Or.inl
                    exact assump_179
                  let assump_183 := assump_140 assump_201
                  apply False.elim assump_183
                let assump_178 := assump_141 assump_200
                apply False.elim assump_178


variable (p1 p0 p7 p2 p4 p5 p6 : Prop)
theorem file90_116485 : (((((p2 → False) ∧ (p2 → False)) ∧ ((p1 ∨ p6) ∧ (True → False))) → False) ∨ ((((p4 ∧ p5) ∧ (p0 ∧ p7)) ∧ ((p0 ∨ False) ∧ (False → False))) ∧ (((p1 ∨ p5) ∧ (True → False)) ∧ ((p1 ∧ p5) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_30 : True := by
            apply True.intro
          let assump_18 := assump_11 assump_30
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_31 : True := by
            apply True.intro
          let assump_26 := assump_11 assump_31
          apply False.elim assump_26


