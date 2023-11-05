variable (p7 p6 p5 p0 p3 p4 p1 : Prop)
theorem file58_47 : ((((((p5 ∧ p0) → False) ∨ ((p4 → False) ∨ (p5 ∧ p7))) ∧ (((p7 ∨ p1) → False) ∧ ((False ∧ p7) ∧ (p3 ∧ p4)))) ∧ ((((p7 → p4) ∧ (False ∨ True)) → ((False ∧ False) → (p6 ∨ p7))) → (((True ∨ p5) → (p5 ∧ p6)) ∧ ((p5 ∨ p4) ∨ (p4 → False))))) → False) := by
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
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case inl assump_20 =>
          cases assump_5
          case intro assump_24 assump_25 =>
            cases assump_25
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                apply False.elim assump_30
        case inr assump_21 =>
          cases assump_21
          case intro assump_34 assump_35 =>
            cases assump_5
            case intro assump_40 assump_41 =>
              cases assump_41
              case intro assump_44 assump_45 =>
                cases assump_44
                case intro assump_46 assump_47 =>
                  apply False.elim assump_46


variable (p3 p1 p6 p0 p4 p7 : Prop)
theorem file58_1500 : ((((((p1 ∧ p6) ∨ (False ∧ p6)) ∨ ((p1 ∧ p7) ∨ (p6 ∧ p4))) ∨ (((False ∧ p7) → (p0 ∨ p7)) ∨ ((p6 → False) ∧ (p1 ∨ p7)))) ∧ ((((p7 → False) ∧ (p1 → False)) → ((p7 → p3) ∨ (p7 → False))) → False)) → False) := by
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
            have assump_177 : (((p7 → False) ∧ (p1 → False)) → ((p7 → p3) ∨ (p7 → False))) := by
              intro assump_19
              cases assump_19
              case intro assump_20 assump_21 =>
                apply Or.inl
                intro assump_26
                have assump_178 : p1 := by
                  exact assump_10
                let assump_30 := assump_21 assump_178
                apply False.elim assump_30
            let assump_18 := assump_3 assump_177
            apply False.elim assump_18
        case inr assump_9 =>
          cases assump_9
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
      case inr assump_7 =>
        cases assump_7
        case inl assump_41 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            have assump_179 : (((p7 → False) ∧ (p1 → False)) → ((p7 → p3) ∨ (p7 → False))) := by
              intro assump_52
              cases assump_52
              case intro assump_53 assump_54 =>
                apply Or.inl
                intro assump_59
                have assump_180 : p1 := by
                  exact assump_43
                let assump_63 := assump_54 assump_180
                apply False.elim assump_63
            let assump_51 := assump_3 assump_179
            apply False.elim assump_51
        case inr assump_42 =>
          cases assump_42
          case intro assump_70 assump_71 =>
            have assump_181 : (((p7 → False) ∧ (p1 → False)) → ((p7 → p3) ∨ (p7 → False))) := by
              intro assump_79
              cases assump_79
              case intro assump_80 assump_81 =>
                apply Or.inl
                intro assump_86
                have assump_182 : p7 := by
                  exact assump_86
                let assump_91 := assump_80 assump_182
                apply False.elim assump_91
            let assump_78 := assump_3 assump_181
            apply False.elim assump_78
    case inr assump_5 =>
      cases assump_5
      case inl assump_98 =>
        have assump_183 : (((p7 → False) ∧ (p1 → False)) → ((p7 → p3) ∨ (p7 → False))) := by
          intro assump_105
          cases assump_105
          case intro assump_106 assump_107 =>
            apply Or.inl
            intro assump_112
            have assump_184 : p7 := by
              exact assump_112
            let assump_117 := assump_106 assump_184
            apply False.elim assump_117
        let assump_104 := assump_3 assump_183
        apply False.elim assump_104
      case inr assump_99 =>
        cases assump_99
        case intro assump_124 assump_125 =>
          cases assump_125
          case inl assump_128 =>
            have assump_185 : (((p7 → False) ∧ (p1 → False)) → ((p7 → p3) ∨ (p7 → False))) := by
              intro assump_135
              cases assump_135
              case intro assump_136 assump_137 =>
                apply Or.inl
                intro assump_142
                have assump_186 : p1 := by
                  exact assump_128
                let assump_146 := assump_137 assump_186
                apply False.elim assump_146
            let assump_134 := assump_3 assump_185
            apply False.elim assump_134
          case inr assump_129 =>
            have assump_187 : (((p7 → False) ∧ (p1 → False)) → ((p7 → p3) ∨ (p7 → False))) := by
              intro assump_158
              cases assump_158
              case intro assump_159 assump_160 =>
                apply Or.inl
                intro assump_165
                have assump_188 : p7 := by
                  exact assump_165
                let assump_170 := assump_159 assump_188
                apply False.elim assump_170
            let assump_157 := assump_3 assump_187
            apply False.elim assump_157


variable (p2 p0 p3 p7 p4 p5 : Prop)
theorem file58_5852 : (((((p4 → False) ∧ (True → p3)) ∧ ((p7 ∧ p0) ∨ (p2 ∧ p5))) → False) → ((((p3 ∧ p2) → False) → ((True → False) ∨ (p2 → True))) → (((False ∧ p5) → False) ∨ ((p7 ∧ p4) → (False → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p7 p6 p0 p3 p5 p4 : Prop)
theorem file58_6252 : (((((True → p6) ∧ (p4 ∨ True)) ∧ ((p3 → False) ∨ (p7 → p6))) → (((p3 ∧ p3) → False) → ((p3 → False) → (p0 ∨ True)))) ∨ ((((p7 → False) ∧ (p0 → False)) ∨ ((p5 → p7) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        cases assump_9
        case inl assump_18 =>
          apply Or.inr
          apply True.intro
        case inr assump_19 =>
          apply Or.inr
          apply True.intro
      case inr assump_15 =>
        cases assump_9
        case inl assump_26 =>
          apply Or.inr
          apply True.intro
        case inr assump_27 =>
          apply Or.inr
          apply True.intro


variable (p0 p1 p5 : Prop)
theorem file58_7111 : (((((p0 → False) ∨ (p1 ∧ False)) → ((True → False) → (p1 ∧ p5))) → False) → False) := by
  intro assump_1
  have assump_44 : (((p0 → False) ∨ (p1 ∧ False)) → ((True → False) → (p1 ∧ p5))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_5
    case inl assump_9 =>
      have assump_45 : True := by
        apply True.intro
      let assump_14 := assump_6 assump_45
      apply False.elim assump_14
    case inr assump_10 =>
      cases assump_10
      case intro assump_18 assump_19 =>
        apply False.elim assump_19
    cases assump_5
    case inl assump_26 =>
      have assump_46 : True := by
        apply True.intro
      let assump_31 := assump_6 assump_46
      apply False.elim assump_31
    case inr assump_27 =>
      cases assump_27
      case intro assump_35 assump_36 =>
        apply False.elim assump_36
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p4 p1 p7 p2 p3 p6 : Prop)
theorem file58_8091 : (((((False ∧ p2) ∧ (p2 ∨ p3)) ∧ ((p1 → p4) ∧ (p1 → False))) → False) ∨ ((((p1 ∧ p2) ∧ (True ∨ p6)) → ((p2 ∨ p4) ∧ (True ∧ p1))) → (((True → p7) ∧ (p4 ∧ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p7 p1 p3 : Prop)
theorem file58_8547 : ((((((True → False) → False) → False) → False) → ((((p3 → p3) ∨ (p1 → p1)) → False) ∧ (((False → False) ∨ (p1 → p7)) ∨ ((p7 ∧ p1) → False)))) → False) := by
  intro assump_1
  have assump_27 : ((((True → False) → False) → False) → False) := by
    intro assump_5
    have assump_28 : ((True → False) → False) := by
      intro assump_9
      have assump_29 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_29
      apply False.elim assump_12
    let assump_8 := assump_5 assump_28
    apply False.elim assump_8
  let assump_4 := assump_1 assump_27
  let assump_19 := And.left assump_4
  have assump_30 : ((p3 → p3) ∨ (p1 → p1)) := by
    apply Or.inl
    intro assump_21
    exact assump_21
  let assump_20 := assump_19 assump_30
  apply False.elim assump_20


variable (p6 p1 p5 p3 p2 p7 p4 : Prop)
theorem file58_9397 : (((((p1 ∨ p3) ∨ (p7 ∨ p2)) → ((p3 → True) ∨ (p1 ∧ p6))) ∨ (((p4 → False) → False) ∨ ((p3 ∧ p1) → False))) ∨ ((((p6 → False) ∧ (p1 ∧ True)) ∨ ((True → p5) ∨ (p7 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      apply True.intro
    case inr assump_5 =>
      apply Or.inl
      intro assump_11
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_12 =>
      apply Or.inl
      intro assump_16
      apply True.intro
    case inr assump_13 =>
      apply Or.inl
      intro assump_19
      apply True.intro


variable (p5 p3 p7 p6 p2 p0 : Prop)
theorem file58_10149 : ((((((p2 → True) → False) ∧ ((p5 → p3) → (p2 → p3))) ∧ (((p2 ∨ p3) ∨ (p5 ∨ p5)) → False)) ∨ ((((p2 → p6) ∧ (p7 ∨ p6)) → False) ∧ (((False ∨ p0) → (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_44 : (p2 → True) := by
          intro assump_26
          apply True.intro
        let assump_25 := assump_6 assump_44
        apply False.elim assump_25
  case inr assump_3 =>
    cases assump_3
    case intro assump_30 assump_31 =>
      have assump_45 : ((False ∨ p0) → (False → False)) := by
        intro assump_37
        intro assump_38
        apply False.elim assump_38
      let assump_36 := assump_31 assump_45
      apply False.elim assump_36


variable (p0 p7 p3 p5 : Prop)
theorem file58_11039 : ((((((p3 ∧ False) ∧ (p7 → False)) → False) ∨ (((p5 → False) ∧ (p5 → p0)) → False)) → False) → False) := by
  intro assump_27
  have assump_43 : ((((p3 ∧ False) ∧ (p7 → False)) → False) ∨ (((p5 → False) ∧ (p5 → p0)) → False)) := by
    apply Or.inl
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        apply False.elim assump_35
  let assump_30 := assump_27 assump_43
  apply False.elim assump_30


variable (p7 p2 p3 : Prop)
theorem file58_11581 : ((((((p3 ∧ True) ∨ (True → False)) → False) → (((False ∨ p2) ∧ (False → False)) → ((p7 ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p3 ∧ True) ∨ (True → False)) → False) → (((False ∨ p2) ∧ (False → False)) → ((p7 ∧ p3) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          apply False.elim assump_16
        case inr assump_17 =>
          have assump_34 : ((p3 ∧ True) ∨ (True → False)) := by
            apply Or.inl
            apply And.intro
            exact assump_9
            apply True.intro
          let assump_26 := assump_5 assump_34
          apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p5 p2 p3 p6 : Prop)
theorem file58_12522 : (((((p3 ∨ True) ∨ (p3 → p2)) ∨ ((p5 → False) ∨ (p2 ∧ p6))) → False) → False) := by
  intro assump_20
  have assump_27 : (((p3 ∨ True) ∨ (p3 → p2)) ∨ ((p5 → False) ∨ (p2 ∧ p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_23 := assump_20 assump_27
  apply False.elim assump_23


variable (p1 : Prop)
theorem file58_12890 : (((((True ∧ False) ∨ (True → False)) → ((False → p1) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : (((True ∧ False) ∨ (True → False)) → ((False → p1) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    case inr assump_10 =>
      have assump_27 : True := by
        apply True.intro
      let assump_19 := assump_10 assump_27
      apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p7 p0 p6 p3 p5 p4 p2 : Prop)
theorem file58_13547 : (((((p3 ∧ p3) ∨ (p0 → p3)) → ((p3 ∧ p5) ∨ (p6 → False))) ∧ (((p4 ∨ p7) → False) ∧ ((True → False) ∧ (p2 → p2)))) → ((((p2 → False) → False) → ((p7 → True) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        have assump_24 : True := by
          apply True.intro
        let assump_20 := assump_13 assump_24
        apply False.elim assump_20


variable (p5 p6 p1 : Prop)
theorem file58_14125 : ((((((True → False) → (p1 → False)) → False) → (((p5 → False) → False) ∧ ((False ∧ p5) ∨ (p6 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((True → False) → (p1 → False)) → False) → (((p5 → False) → False) ∧ ((False ∧ p5) ∨ (p6 ∨ p5)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_45 : ((True → False) → (p1 → False)) := by
      intro assump_12
      intro assump_13
      have assump_46 : True := by
        apply True.intro
      let assump_18 := assump_12 assump_46
      apply False.elim assump_18
    let assump_11 := assump_5 assump_45
    apply False.elim assump_11
    have assump_47 : ((True → False) → (p1 → False)) := by
      intro assump_28
      intro assump_29
      have assump_48 : True := by
        apply True.intro
      let assump_34 := assump_28 assump_48
      apply False.elim assump_34
    let assump_27 := assump_5 assump_47
    apply False.elim assump_27
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p2 p6 p4 p3 p1 p0 : Prop)
theorem file58_15194 : (((((p6 → True) → False) ∨ ((p3 ∧ p0) → (p6 → p6))) → False) → ((((p6 → False) → False) ∧ ((p0 ∨ False) → (p3 ∨ p2))) → (((p2 ∧ p4) ∨ (False → False)) ∧ ((True ∧ p1) → (p1 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inr
    intro assump_11
    apply False.elim assump_11
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_2
    case intro assump_21 assump_22 =>
      apply Or.inl
      exact assump_16


variable (p6 p7 p0 p1 p3 p5 p4 p2 : Prop)
theorem file58_15789 : (((((p4 ∨ p3) → False) → ((p5 ∨ p5) → False)) → (((p6 ∨ False) ∧ (p0 ∨ p6)) ∧ ((p6 ∨ p6) → (p7 ∨ p5)))) → ((((False → False) ∨ (p6 ∨ True)) ∨ ((p2 ∨ p5) → (False ∨ p5))) ∧ (((p6 → False) → False) → ((p4 ∨ True) ∨ (p7 ∨ p1))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p2 p6 p7 p4 p3 p1 p5 : Prop)
theorem file58_16261 : (((((p2 → False) → (p4 → p3)) → False) ∧ (((p7 ∨ p7) ∧ (True ∧ p6)) ∧ ((p5 → False) ∧ (p2 ∧ p1)))) → ((((p1 → p3) ∧ (p4 → p3)) → ((p5 ∨ p7) → False)) → False)) := by
  intro assump_29
  intro assump_30
  cases assump_29
  case intro assump_33 assump_34 =>
    cases assump_34
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_39
        case inl assump_41 =>
          cases assump_40
          case intro assump_45 assump_46 =>
            cases assump_38
            case intro assump_51 assump_52 =>
              cases assump_52
              case intro assump_55 assump_56 =>
                have assump_117 : ((p2 → False) → (p4 → p3)) := by
                  intro assump_67
                  intro assump_68
                  have assump_118 : p2 := by
                    exact assump_55
                  let assump_73 := assump_67 assump_118
                  apply False.elim assump_73
                let assump_66 := assump_33 assump_117
                apply False.elim assump_66
        case inr assump_42 =>
          cases assump_40
          case intro assump_82 assump_83 =>
            cases assump_38
            case intro assump_88 assump_89 =>
              cases assump_89
              case intro assump_92 assump_93 =>
                have assump_119 : ((p2 → False) → (p4 → p3)) := by
                  intro assump_104
                  intro assump_105
                  have assump_120 : p2 := by
                    exact assump_92
                  let assump_110 := assump_104 assump_120
                  apply False.elim assump_110
                let assump_103 := assump_33 assump_119
                apply False.elim assump_103


variable (p1 p0 p6 p2 p3 p5 p4 : Prop)
theorem file58_18063 : ((((((p0 → False) → False) ∨ ((p2 ∨ p4) ∧ (p3 ∨ False))) ∧ (((p5 ∧ p2) → (False → p1)) ∧ ((p0 ∧ False) ∧ (p6 → p4)))) ∨ ((((p1 ∧ False) → (p5 → True)) ∨ ((p1 ∧ False) → (p0 ∨ p5))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
      case inr assump_11 =>
        cases assump_11
        case intro assump_26 assump_27 =>
          cases assump_26
          case inl assump_28 =>
            cases assump_27
            case inl assump_32 =>
              cases assump_9
              case intro assump_36 assump_37 =>
                cases assump_37
                case intro assump_40 assump_41 =>
                  cases assump_40
                  case intro assump_42 assump_43 =>
                    apply False.elim assump_43
            case inr assump_33 =>
              apply False.elim assump_33
          case inr assump_29 =>
            cases assump_27
            case inl assump_52 =>
              cases assump_9
              case intro assump_56 assump_57 =>
                cases assump_57
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    apply False.elim assump_63
            case inr assump_53 =>
              apply False.elim assump_53
  case inr assump_7 =>
    have assump_78 : (((p1 ∧ False) → (p5 → True)) ∨ ((p1 ∧ False) → (p0 ∨ p5))) := by
      apply Or.inl
      intro assump_73
      intro assump_74
      apply True.intro
    let assump_72 := assump_7 assump_78
    apply False.elim assump_72


variable (p5 p1 p4 p0 p7 : Prop)
theorem file58_20046 : (((((False → False) → False) → ((p7 → False) → False)) ∧ (((p1 → False) → (p1 → False)) → ((p7 ∨ True) → False))) → ((((p5 → False) → False) ∧ ((p0 → p4) ∨ (p1 → p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        have assump_55 : ((p1 → False) → (p1 → False)) := by
          intro assump_18
          intro assump_19
          have assump_56 : p1 := by
            exact assump_19
          let assump_24 := assump_18 assump_56
          apply False.elim assump_24
        let assump_17 := assump_12 assump_55
        have assump_57 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_28 := assump_17 assump_57
        apply False.elim assump_28
    case inr assump_8 =>
      cases assump_1
      case intro assump_34 assump_35 =>
        have assump_58 : ((p1 → False) → (p1 → False)) := by
          intro assump_41
          intro assump_42
          have assump_59 : p1 := by
            exact assump_42
          let assump_47 := assump_41 assump_59
          apply False.elim assump_47
        let assump_40 := assump_35 assump_58
        have assump_60 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_51 := assump_40 assump_60
        apply False.elim assump_51


variable (p3 p0 p2 p4 p5 p6 p1 : Prop)
theorem file58_21527 : (((((p0 ∧ p3) → (False → p2)) → False) → (((p5 → p3) ∧ (p3 ∧ p6)) ∧ ((False → p2) → (p2 ∧ p1)))) ∨ ((((False ∧ p3) → (True → False)) ∨ ((p6 → True) ∨ (p2 ∧ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_60 : ((p0 ∧ p3) → (False → p2)) := by
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_60
  apply False.elim assump_7
  apply And.intro
  have assump_61 : ((p0 ∧ p3) → (False → p2)) := by
    intro assump_18
    intro assump_19
    apply False.elim assump_19
  let assump_17 := assump_1 assump_61
  apply False.elim assump_17
  have assump_62 : ((p0 ∧ p3) → (False → p2)) := by
    intro assump_28
    intro assump_29
    apply False.elim assump_29
  let assump_27 := assump_1 assump_62
  apply False.elim assump_27
  intro assump_35
  apply And.intro
  have assump_63 : ((p0 ∧ p3) → (False → p2)) := by
    intro assump_41
    intro assump_42
    apply False.elim assump_42
  let assump_40 := assump_1 assump_63
  apply False.elim assump_40
  have assump_64 : ((p0 ∧ p3) → (False → p2)) := by
    intro assump_53
    intro assump_54
    apply False.elim assump_54
  let assump_52 := assump_1 assump_64
  apply False.elim assump_52


variable (p0 p2 p6 p1 : Prop)
theorem file58_22843 : (((((False → False) ∨ (p0 ∨ False)) → ((p0 ∨ True) → False)) ∧ (((p0 → p1) ∨ (p6 → False)) ∨ ((p0 ∧ p2) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_43 : ((False → False) ∨ (p0 ∨ False)) := by
          apply Or.inl
          intro assump_14
          apply False.elim assump_14
        let assump_13 := assump_2 assump_43
        have assump_44 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_17 := assump_13 assump_44
        apply False.elim assump_17
      case inr assump_9 =>
        have assump_45 : ((False → False) ∨ (p0 ∨ False)) := by
          apply Or.inl
          intro assump_25
          apply False.elim assump_25
        let assump_24 := assump_2 assump_45
        have assump_46 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_28 := assump_24 assump_46
        apply False.elim assump_28
    case inr assump_7 =>
      have assump_47 : ((False → False) ∨ (p0 ∨ False)) := by
        apply Or.inl
        intro assump_36
        apply False.elim assump_36
      let assump_35 := assump_2 assump_47
      have assump_48 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_39 := assump_35 assump_48
      apply False.elim assump_39


variable (p1 p6 p2 p0 p3 : Prop)
theorem file58_24323 : (((((p1 → False) ∧ (p1 ∧ False)) → ((p1 ∧ p0) ∨ (False ∧ p1))) → False) → ((((p3 → False) → False) ∧ ((p0 ∧ p0) ∨ (True ∧ p6))) → (((True ∧ p2) → False) ∧ ((p3 → False) → (True ∨ p6))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_87 : (((p1 → False) ∧ (p1 ∧ False)) → ((p1 ∧ p0) ∨ (False ∧ p1))) := by
            intro assump_25
            cases assump_25
            case intro assump_26 assump_27 =>
              cases assump_27
              case intro assump_30 assump_31 =>
                apply False.elim assump_31
          let assump_24 := assump_1 assump_87
          apply False.elim assump_24
      case inr assump_15 =>
        cases assump_15
        case intro assump_39 assump_40 =>
          have assump_88 : (((p1 → False) ∧ (p1 ∧ False)) → ((p1 ∧ p0) ∨ (False ∧ p1))) := by
            intro assump_48
            cases assump_48
            case intro assump_49 assump_50 =>
              cases assump_50
              case intro assump_53 assump_54 =>
                apply False.elim assump_54
          let assump_47 := assump_1 assump_88
          apply False.elim assump_47
  intro assump_62
  cases assump_2
  case intro assump_65 assump_66 =>
    cases assump_66
    case inl assump_69 =>
      cases assump_69
      case intro assump_71 assump_72 =>
        apply Or.inl
        apply True.intro
    case inr assump_70 =>
      cases assump_70
      case intro assump_79 assump_80 =>
        apply Or.inl
        apply True.intro


variable (p7 p3 p6 p1 p0 p4 : Prop)
theorem file58_26122 : ((((((p6 → False) ∧ (p0 → p3)) ∧ ((False → p7) ∧ (p4 ∧ False))) → (((p7 → False) ∧ (p6 → False)) ∨ ((p0 → p3) ∨ (p3 → p1)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p6 → False) ∧ (p0 → p3)) ∧ ((False → p7) ∧ (p4 ∧ False))) → (((p7 → False) ∧ (p6 → False)) ∨ ((p0 → p3) ∨ (p3 → p1)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p7 p0 p4 p2 p1 : Prop)
theorem file58_26865 : (((((True → False) → (p2 ∧ p1)) → False) → (((p7 → p0) → False) ∧ ((False ∨ p4) ∨ (p1 ∨ p0)))) ∨ ((((p1 → False) ∧ (p7 → p1)) ∧ ((p0 ∧ p4) → (p7 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_43 : ((True → False) → (p2 ∧ p1)) := by
    intro assump_8
    apply And.intro
    have assump_44 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_44
    apply False.elim assump_11
    have assump_45 : True := by
      apply True.intro
    let assump_17 := assump_8 assump_45
    apply False.elim assump_17
  let assump_7 := assump_1 assump_43
  apply False.elim assump_7
  have assump_46 : ((True → False) → (p2 ∧ p1)) := by
    intro assump_27
    apply And.intro
    have assump_47 : True := by
      apply True.intro
    let assump_30 := assump_27 assump_47
    apply False.elim assump_30
    have assump_48 : True := by
      apply True.intro
    let assump_36 := assump_27 assump_48
    apply False.elim assump_36
  let assump_26 := assump_1 assump_46
  apply False.elim assump_26


variable (p7 p2 p1 p0 p3 p4 : Prop)
theorem file58_27988 : ((((((p7 → False) ∧ (p1 → p0)) → ((True ∧ True) → (False → False))) ∨ (((p1 ∧ p7) ∨ (p1 → False)) → ((p2 → False) → (p3 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p7 → False) ∧ (p1 → p0)) → ((True ∧ True) → (False → False))) ∨ (((p1 ∧ p7) ∨ (p1 → False)) → ((p2 → False) → (p3 ∨ p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p2 p1 p5 p3 p0 : Prop)
theorem file58_28539 : ((((((p7 → p5) ∧ (p7 ∨ p1)) ∨ ((p5 → p0) ∧ (p5 ∨ True))) → (((False → p2) → (p3 → False)) → ((False ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 → p5) ∧ (p7 ∨ p1)) ∨ ((p5 → p0) ∧ (p5 ∨ True))) → (((False → p2) → (p3 → False)) → ((False ∧ p1) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p4 p6 p0 p7 p1 p2 p3 : Prop)
theorem file58_29112 : ((((((p2 ∨ p2) ∨ (p1 ∧ p4)) ∨ ((False ∧ True) ∧ (p6 → True))) ∨ (((p5 ∧ p7) ∧ (p6 ∨ p5)) → ((p3 ∨ p0) ∨ (p6 → p5)))) → ((((p3 → p0) → False) → ((p0 ∧ False) → False)) → False)) → False) := by
  intro assump_1
  have assump_38 : ((((p2 ∨ p2) ∨ (p1 ∧ p4)) ∨ ((False ∧ True) ∧ (p6 → True))) ∨ (((p5 ∧ p7) ∧ (p6 ∨ p5)) → ((p3 ∨ p0) ∨ (p6 → p5)))) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inr
          intro assump_18
          exact assump_8
        case inr assump_15 =>
          apply Or.inr
          intro assump_23
          exact assump_15
  let assump_4 := assump_1 assump_38
  have assump_39 : (((p3 → p0) → False) → ((p0 ∧ False) → False)) := by
    intro assump_27
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      apply False.elim assump_30
  let assump_26 := assump_4 assump_39
  apply False.elim assump_26


variable (p1 p3 p4 p2 p0 p7 p5 : Prop)
theorem file58_30213 : (((((p5 → False) ∨ (p7 ∧ True)) → ((p4 ∨ p2) → (p7 ∨ False))) → (((False → p0) ∧ (False → False)) ∧ ((p1 ∨ True) ∨ (p2 ∧ p1)))) ∨ ((((True ∨ p5) → False) → False) ∧ (((p1 ∧ p2) → (False → False)) ∧ ((p5 → p3) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  apply False.elim assump_5
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p7 p5 p4 p3 p1 p6 p2 : Prop)
theorem file58_30717 : (((((True ∧ p2) → (p4 ∧ True)) ∧ ((p1 ∧ p3) ∨ (p3 → p6))) ∧ (((p7 ∨ p2) ∨ (p2 ∧ p5)) ∧ ((p1 ∨ p6) → False))) → ((((False ∨ p6) → False) ∧ ((False ∨ p1) ∧ (p6 → False))) → False)) := by
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
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_20
            case inl assump_23 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                cases assump_18
                case intro assump_31 assump_32 =>
                  cases assump_31
                  case inl assump_33 =>
                    cases assump_33
                    case inl assump_35 =>
                      have assump_101 : (p1 ∨ p6) := by
                        apply Or.inl
                        exact assump_25
                      let assump_41 := assump_32 assump_101
                      apply False.elim assump_41
                    case inr assump_36 =>
                      have assump_102 : (p1 ∨ p6) := by
                        apply Or.inl
                        exact assump_25
                      let assump_49 := assump_32 assump_102
                      apply False.elim assump_49
                  case inr assump_34 =>
                    cases assump_34
                    case intro assump_53 assump_54 =>
                      have assump_103 : (p1 ∨ p6) := by
                        apply Or.inl
                        exact assump_25
                      let assump_61 := assump_32 assump_103
                      apply False.elim assump_61
            case inr assump_24 =>
              cases assump_18
              case intro assump_67 assump_68 =>
                cases assump_67
                case inl assump_69 =>
                  cases assump_69
                  case inl assump_71 =>
                    have assump_104 : (p1 ∨ p6) := by
                      apply Or.inl
                      exact assump_10
                    let assump_77 := assump_68 assump_104
                    apply False.elim assump_77
                  case inr assump_72 =>
                    have assump_105 : (p1 ∨ p6) := by
                      apply Or.inl
                      exact assump_10
                    let assump_85 := assump_68 assump_105
                    apply False.elim assump_85
                case inr assump_70 =>
                  cases assump_70
                  case intro assump_89 assump_90 =>
                    have assump_106 : (p1 ∨ p6) := by
                      apply Or.inl
                      exact assump_10
                    let assump_97 := assump_68 assump_106
                    apply False.elim assump_97


variable (p5 p6 p4 p7 p0 p1 p3 p2 : Prop)
theorem file58_33741 : (((((p4 → False) → False) → False) ∧ (((p2 ∨ False) → (True ∧ p3)) → ((p0 → True) → False))) → ((((p4 ∨ p3) ∧ (p1 ∧ p0)) ∧ ((p6 → False) → False)) ∨ (((p2 ∧ p3) ∨ (p1 ∨ p4)) → ((p7 ∨ p3) ∨ (p5 ∨ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inr
        exact assump_12
    case inr assump_10 =>
      cases assump_10
      case inl assump_17 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
      case inr assump_18 =>
        apply Or.inr
        apply Or.inr
        apply True.intro


variable (p5 p2 p0 p1 p7 p4 p6 p3 : Prop)
theorem file58_34531 : (((((p1 → p0) ∨ (p0 → p2)) ∧ ((p1 ∧ p7) → (False → False))) ∨ (((p6 ∨ p4) ∧ (p7 ∨ p0)) ∨ ((False → False) → False))) → ((((p1 ∧ p3) ∧ (p5 → p6)) → ((p6 → p1) → False)) → (((True ∨ p4) ∨ (p1 → p3)) ∨ ((False → True) → (False ∨ True))))) := by
  intro assump_229
  intro assump_230
  cases assump_229
  case inl assump_233 =>
    cases assump_233
    case intro assump_235 assump_236 =>
      cases assump_235
      case inl assump_237 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_238 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
  case inr assump_234 =>
    cases assump_234
    case inl assump_247 =>
      cases assump_247
      case intro assump_249 assump_250 =>
        cases assump_249
        case inl assump_251 =>
          cases assump_250
          case inl assump_255 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_256 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
        case inr assump_252 =>
          cases assump_250
          case inl assump_263 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_264 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
    case inr assump_248 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p0 p4 p1 : Prop)
theorem file58_36158 : ((((((True ∨ True) ∨ (p1 → False)) → False) → (((p4 → False) ∨ (p4 ∨ p0)) → False)) → False) → False) := by
  intro assump_10
  have assump_47 : ((((True ∨ True) ∨ (p1 → False)) → False) → (((p4 → False) ∨ (p4 ∨ p0)) → False)) := by
    intro assump_14
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      have assump_48 : ((True ∨ True) ∨ (p1 → False)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_22 := assump_14 assump_48
      apply False.elim assump_22
    case inr assump_17 =>
      cases assump_17
      case inl assump_26 =>
        have assump_49 : ((True ∨ True) ∨ (p1 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_32 := assump_14 assump_49
        apply False.elim assump_32
      case inr assump_27 =>
        have assump_50 : ((True ∨ True) ∨ (p1 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_40 := assump_14 assump_50
        apply False.elim assump_40
  let assump_13 := assump_10 assump_47
  apply False.elim assump_13


variable (p4 p1 p5 p3 p7 p0 : Prop)
theorem file58_37342 : (((((False ∧ p5) → False) ∨ ((p1 ∨ p1) ∨ (p7 → False))) ∨ (((False → p4) → False) ∧ ((p4 ∨ p5) → False))) ∧ ((((p1 → False) → (p3 → False)) ∧ ((p1 ∧ p0) ∧ (p1 → False))) → False)) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    apply False.elim assump_15
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        have assump_38 : p1 := by
          exact assump_26
        let assump_34 := assump_25 assump_38
        apply False.elim assump_34


variable (p6 p4 p1 p3 p2 p7 p5 : Prop)
theorem file58_38074 : (((((p3 → False) ∧ (p5 ∧ True)) ∨ ((p2 ∨ p7) → False)) ∧ (((True ∨ p4) → False) ∨ ((True ∨ p1) → False))) → ((((p1 → False) ∨ (p4 ∧ p6)) → ((p2 ∨ p4) ∨ (True ∨ p5))) → False)) := by
  intro assump_11
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          cases assump_16
          case inl assump_29 =>
            have assump_59 : (True ∨ p4) := by
              apply Or.inl
              apply True.intro
            let assump_33 := assump_29 assump_59
            apply False.elim assump_33
          case inr assump_30 =>
            have assump_60 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_39 := assump_30 assump_60
            apply False.elim assump_39
    case inr assump_18 =>
      cases assump_16
      case inl assump_45 =>
        have assump_61 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_49 := assump_45 assump_61
        apply False.elim assump_49
      case inr assump_46 =>
        have assump_62 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_55 := assump_46 assump_62
        apply False.elim assump_55


variable (p1 p3 p0 p6 : Prop)
theorem file58_39500 : ((((((p3 ∨ p1) ∧ (False → False)) → False) → (((True ∨ p3) → False) → ((p6 ∨ p0) → (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_42 : ((((p3 ∨ p1) ∧ (False → False)) → False) → (((True ∨ p3) → False) → ((p6 ∨ p0) → (p1 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      have assump_43 : ((p3 ∨ p1) ∧ (False → False)) := by
        apply And.intro
        apply Or.inr
        exact assump_8
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_5 assump_43
      apply False.elim assump_19
    case inr assump_12 =>
      have assump_44 : ((p3 ∨ p1) ∧ (False → False)) := by
        apply And.intro
        apply Or.inr
        exact assump_8
        intro assump_33
        apply False.elim assump_33
      let assump_32 := assump_5 assump_44
      apply False.elim assump_32
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p0 p7 p6 p1 p3 p2 p4 : Prop)
theorem file58_40559 : ((((((p6 ∨ p0) → False) ∨ ((True ∧ False) → False)) ∨ (((p6 → False) ∨ (p0 → p7)) → False)) ∧ ((((True ∨ p0) ∨ (p3 → False)) ∨ ((p4 → True) ∧ (p1 → p2))) → False)) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        have assump_37 : (((True ∨ p0) ∨ (p3 → False)) ∨ ((p4 → True) ∧ (p1 → p2))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_17 := assump_8 assump_37
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_38 : (((True ∨ p0) ∨ (p3 → False)) ∨ ((p4 → True) ∧ (p1 → p2))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_25 := assump_8 assump_38
        apply False.elim assump_25
    case inr assump_10 =>
      have assump_39 : (((True ∨ p0) ∨ (p3 → False)) ∨ ((p4 → True) ∧ (p1 → p2))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_33 := assump_8 assump_39
      apply False.elim assump_33


variable (p5 p3 p1 p2 p4 p0 : Prop)
theorem file58_41794 : (((((p4 ∨ True) ∨ (p3 ∧ True)) ∨ ((p4 ∧ p1) → False)) ∨ (((p5 ∧ p5) ∧ (p0 → p2)) ∧ ((p5 → p3) ∨ (p2 → p2)))) ∨ ((((p4 → False) → (p0 → p1)) → False) → (((p2 → False) → (False ∨ p4)) ∨ ((True → False) ∧ (p4 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p6 p5 p2 p0 p7 p1 p4 : Prop)
theorem file58_42176 : ((((((p4 ∨ p4) → (p0 ∨ p2)) ∧ ((p2 → False) ∨ (p1 → False))) → (((p7 ∨ p5) → (p2 ∨ p7)) ∨ ((p5 → False) → (p0 ∨ p6)))) ∧ ((((p7 ∧ p6) ∧ (False ∧ p0)) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_29 : (((p7 ∧ p6) ∧ (False ∧ p0)) → False) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
    let assump_12 := assump_7 assump_29
    apply False.elim assump_12


variable (p3 : Prop)
theorem file58_42867 : (((((True ∨ p3) → False) → False) → False) → False) := by
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


variable (p3 p1 p2 p6 : Prop)
theorem file58_43287 : (((((p3 ∧ False) → False) → False) ∧ (((p2 ∨ False) ∧ (p6 ∧ p1)) ∨ ((p6 ∧ p1) ∨ (False ∧ True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            have assump_61 : ((p3 ∧ False) → False) := by
              intro assump_24
              cases assump_24
              case intro assump_25 assump_26 =>
                apply False.elim assump_26
            let assump_23 := assump_2 assump_61
            apply False.elim assump_23
        case inr assump_11 =>
          apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case inl assump_36 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          have assump_62 : ((p3 ∧ False) → False) := by
            intro assump_47
            cases assump_47
            case intro assump_48 assump_49 =>
              apply False.elim assump_49
          let assump_46 := assump_2 assump_62
          apply False.elim assump_46
      case inr assump_37 =>
        cases assump_37
        case intro assump_57 assump_58 =>
          apply False.elim assump_57


variable (p0 p1 p2 p3 p6 p7 p4 p5 : Prop)
theorem file58_44675 : (((((p1 → False) → (p6 → False)) ∨ ((p2 ∨ p5) ∧ (p3 → p6))) → (((p5 ∨ p5) → (False → False)) → False)) → ((((p7 ∨ p1) → (p0 → False)) → ((p2 ∨ p4) → False)) → (((p4 → False) ∧ (p4 ∧ p5)) → ((p0 ∧ p7) ∨ (True ∨ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      apply Or.inr
      apply Or.inl
      apply True.intro


variable (p2 p0 p3 p6 p1 : Prop)
theorem file58_45174 : (((((p1 ∧ p1) → (p0 ∧ p1)) ∨ ((p2 ∨ True) → False)) ∧ (((p1 → False) ∨ (p3 ∨ p6)) ∧ ((True ∨ True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_70 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_16 := assump_9 assump_70
          apply False.elim assump_16
        case inr assump_11 =>
          cases assump_11
          case inl assump_20 =>
            have assump_71 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_26 := assump_9 assump_71
            apply False.elim assump_26
          case inr assump_21 =>
            have assump_72 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_34 := assump_9 assump_72
            apply False.elim assump_34
    case inr assump_5 =>
      cases assump_3
      case intro assump_40 assump_41 =>
        cases assump_40
        case inl assump_42 =>
          have assump_73 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_48 := assump_41 assump_73
          apply False.elim assump_48
        case inr assump_43 =>
          cases assump_43
          case inl assump_52 =>
            have assump_74 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_58 := assump_41 assump_74
            apply False.elim assump_58
          case inr assump_53 =>
            have assump_75 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_66 := assump_41 assump_75
            apply False.elim assump_66


variable (p2 p5 p6 p3 : Prop)
theorem file58_47104 : ((((((False ∧ p6) ∨ (p6 ∨ p5)) ∧ ((p5 ∧ p2) → (p6 ∧ p6))) → False) ∧ ((((p6 → p6) ∨ (p3 → False)) ∨ ((p2 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p6 → p6) ∨ (p3 → False)) ∨ ((p2 → False) → False)) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p7 p4 p1 p6 p5 p0 : Prop)
theorem file58_47614 : (((((p6 ∧ p1) → (True ∨ p4)) → False) ∧ (((p6 ∧ p5) ∧ (p1 → p6)) → False)) → ((((True ∧ p6) ∨ (p3 ∨ True)) ∧ ((p6 → False) → False)) ∨ (((p3 ∨ p7) ∨ (True → p7)) ∨ ((p4 → False) ∨ (p1 → p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply Or.inr
    apply True.intro
    intro assump_8
    have assump_24 : ((p6 ∧ p1) → (True ∨ p4)) := by
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        apply Or.inl
        apply True.intro
    let assump_13 := assump_2 assump_24
    apply False.elim assump_13


variable (p4 p5 p6 : Prop)
theorem file58_48298 : ((((((True ∨ p5) → False) ∧ ((p6 ∧ p4) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((True ∨ p5) → False) ∧ ((p6 ∧ p4) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : (True ∨ p5) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p3 p0 p5 p2 p4 p6 : Prop)
theorem file58_48842 : ((((((p4 ∨ True) ∧ (p4 ∨ p0)) ∧ ((p0 ∧ p3) → False)) ∧ (((True ∨ p6) ∧ (True → False)) → False)) ∧ ((((p3 → False) ∧ (False ∧ p3)) ∧ ((False ∧ p5) → (p3 ∨ p4))) ∧ (((p2 → False) ∨ (p7 ∨ True)) → False))) → False) := by
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
            cases assump_9
            case inl assump_14 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    cases assump_27
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_30
            case inr assump_15 =>
              cases assump_3
              case intro assump_40 assump_41 =>
                cases assump_40
                case intro assump_42 assump_43 =>
                  cases assump_42
                  case intro assump_44 assump_45 =>
                    cases assump_45
                    case intro assump_48 assump_49 =>
                      apply False.elim assump_48
          case inr assump_11 =>
            cases assump_9
            case inl assump_54 =>
              cases assump_3
              case intro assump_62 assump_63 =>
                cases assump_62
                case intro assump_64 assump_65 =>
                  cases assump_64
                  case intro assump_66 assump_67 =>
                    cases assump_67
                    case intro assump_70 assump_71 =>
                      apply False.elim assump_70
            case inr assump_55 =>
              cases assump_3
              case intro assump_80 assump_81 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  cases assump_82
                  case intro assump_84 assump_85 =>
                    cases assump_85
                    case intro assump_88 assump_89 =>
                      apply False.elim assump_88


variable (p5 p6 p0 p7 p3 p4 p2 : Prop)
theorem file58_51184 : (((((p0 → False) ∧ (p3 → False)) → ((False ∨ False) → False)) ∨ (((p6 → False) ∨ (p4 → False)) ∨ ((p6 → p2) ∧ (p7 ∨ p5)))) ∨ ((((p0 ∧ p2) ∧ (False ∨ p4)) → False) ∨ (((p0 ∨ p0) ∧ (p3 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply False.elim assump_3
  case inr assump_4 =>
    apply False.elim assump_4


variable (p1 p0 p5 p4 p3 : Prop)
theorem file58_51638 : ((((((True → p1) → (False → False)) ∨ ((p3 → p4) → False)) ∨ (((p1 ∧ p5) ∨ (p1 ∨ p3)) ∨ ((p0 → p3) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((True → p1) → (False → False)) ∨ ((p3 → p4) → False)) ∨ (((p1 ∧ p5) ∨ (p1 ∨ p3)) ∨ ((p0 → p3) ∨ (False → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p6 p2 p1 p0 p4 : Prop)
theorem file58_52169 : ((((((False ∨ p0) → (p0 → False)) → ((p0 ∧ p2) ∨ (True → False))) → False) ∧ ((((p1 ∨ p1) ∧ (True → False)) → ((p4 ∨ p1) ∧ (p7 ∧ p6))) → False)) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    have assump_84 : (((p1 ∨ p1) ∧ (True → False)) → ((p4 ∨ p1) ∧ (p7 ∧ p6))) := by
      intro assump_28
      apply And.intro
      cases assump_28
      case intro assump_29 assump_30 =>
        cases assump_29
        case inl assump_31 =>
          apply Or.inr
          exact assump_31
        case inr assump_32 =>
          apply Or.inr
          exact assump_32
      apply And.intro
      cases assump_28
      case intro assump_41 assump_42 =>
        cases assump_41
        case inl assump_43 =>
          have assump_85 : True := by
            apply True.intro
          let assump_49 := assump_42 assump_85
          apply False.elim assump_49
        case inr assump_44 =>
          have assump_86 : True := by
            apply True.intro
          let assump_57 := assump_42 assump_86
          apply False.elim assump_57
      cases assump_28
      case intro assump_61 assump_62 =>
        cases assump_61
        case inl assump_63 =>
          have assump_87 : True := by
            apply True.intro
          let assump_69 := assump_62 assump_87
          apply False.elim assump_69
        case inr assump_64 =>
          have assump_88 : True := by
            apply True.intro
          let assump_77 := assump_62 assump_88
          apply False.elim assump_77
    let assump_27 := assump_22 assump_84
    apply False.elim assump_27


variable (p0 p5 p1 p4 p7 p3 p2 : Prop)
theorem file58_53826 : (((((p5 ∧ p4) ∨ (p5 ∧ p5)) → False) ∧ (((p5 ∨ p3) → False) ∧ ((False ∨ p4) ∧ (p3 → False)))) → ((((p7 ∧ p7) → False) → ((p2 ∧ p7) → (p1 ∨ p7))) ∨ (((p0 → p7) → False) ∨ ((p0 → p7) ∧ (p0 → p7))))) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          apply False.elim assump_23
        case inr assump_24 =>
          apply Or.inl
          intro assump_31
          intro assump_32
          cases assump_32
          case intro assump_33 assump_34 =>
            apply Or.inr
            exact assump_34


variable (p1 p2 p4 p7 : Prop)
theorem file58_54593 : ((((((False → p2) ∨ (False → False)) → False) → (((p2 → False) → False) → False)) ∧ ((((p7 ∧ p7) ∨ (p7 → True)) ∨ ((p1 ∧ p4) → False)) → False)) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    have assump_27 : (((p7 ∧ p7) ∨ (p7 → True)) ∨ ((p1 ∧ p4) → False)) := by
      apply Or.inl
      apply Or.inr
      intro assump_23
      apply True.intro
    let assump_22 := assump_17 assump_27
    apply False.elim assump_22


variable (p3 p1 p2 p4 p6 p5 p0 p7 : Prop)
theorem file58_55123 : (((((p7 → p0) ∧ (p7 → True)) ∧ ((p6 → p7) → (p3 ∨ p1))) → (((True ∨ p5) ∧ (False ∧ p5)) → False)) ∨ ((((p2 ∧ p7) ∧ (p5 ∧ p6)) → False) → (((True → p2) ∧ (p2 ∧ p6)) ∨ ((p5 → p4) ∧ (p3 → False))))) := by
  apply Or.inl
  intro assump_16
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case inl assump_20 =>
      cases assump_19
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
    case inr assump_21 =>
      cases assump_19
      case intro assump_30 assump_31 =>
        apply False.elim assump_30


variable (p6 : Prop)
theorem file58_55741 : (((((p6 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p6 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p6 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p0 p1 p7 p2 p3 p5 p4 : Prop)
theorem file58_56175 : ((((((p5 ∧ True) ∧ (True ∧ p2)) ∨ ((p4 ∧ p7) ∨ (p5 → False))) → (((p6 ∧ p0) ∧ (p3 → False)) ∨ ((True → p3) ∧ (p0 → p3)))) ∧ ((((False → False) ∨ (p6 → p1)) ∧ ((True ∨ p4) ∨ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((False → False) ∨ (p6 → p1)) ∧ ((True ∨ p4) ∨ (p3 → False))) := by
      apply And.intro
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p7 p4 p5 p1 p2 p0 : Prop)
theorem file58_56830 : (((((False → False) → False) → False) ∨ (((p4 ∧ p4) → (p2 ∨ p2)) ∨ ((p5 ∨ True) ∨ (p2 → p5)))) ∨ ((((p1 ∨ p7) ∧ (p0 ∧ p5)) ∨ ((p5 ∧ False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p3 p1 p7 p5 p2 : Prop)
theorem file58_57257 : ((((((p2 ∧ p4) → (p3 ∧ False)) ∨ ((p3 → False) ∧ (p2 ∨ p1))) ∨ (((p2 → False) → False) → ((p7 ∨ p5) ∧ (p2 → False)))) ∧ ((((False ∨ p2) → False) ∧ ((False → False) → False)) ∧ (((p2 → p2) ∨ (p7 → False)) ∧ ((p7 → True) ∧ (True → False))))) → False) := by
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
            cases assump_11
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_19
                case intro assump_24 assump_25 =>
                  have assump_166 : True := by
                    apply True.intro
                  let assump_30 := assump_25 assump_166
                  apply False.elim assump_30
              case inr assump_21 =>
                cases assump_19
                case intro assump_36 assump_37 =>
                  have assump_167 : True := by
                    apply True.intro
                  let assump_42 := assump_37 assump_167
                  apply False.elim assump_42
      case inr assump_7 =>
        cases assump_7
        case intro assump_46 assump_47 =>
          cases assump_47
          case inl assump_50 =>
            cases assump_3
            case intro assump_54 assump_55 =>
              cases assump_54
              case intro assump_56 assump_57 =>
                cases assump_55
                case intro assump_62 assump_63 =>
                  cases assump_62
                  case inl assump_64 =>
                    cases assump_63
                    case intro assump_68 assump_69 =>
                      have assump_168 : True := by
                        apply True.intro
                      let assump_74 := assump_69 assump_168
                      apply False.elim assump_74
                  case inr assump_65 =>
                    cases assump_63
                    case intro assump_80 assump_81 =>
                      have assump_169 : True := by
                        apply True.intro
                      let assump_86 := assump_81 assump_169
                      apply False.elim assump_86
          case inr assump_51 =>
            cases assump_3
            case intro assump_92 assump_93 =>
              cases assump_92
              case intro assump_94 assump_95 =>
                cases assump_93
                case intro assump_100 assump_101 =>
                  cases assump_100
                  case inl assump_102 =>
                    cases assump_101
                    case intro assump_106 assump_107 =>
                      have assump_170 : True := by
                        apply True.intro
                      let assump_112 := assump_107 assump_170
                      apply False.elim assump_112
                  case inr assump_103 =>
                    cases assump_101
                    case intro assump_118 assump_119 =>
                      have assump_171 : True := by
                        apply True.intro
                      let assump_124 := assump_119 assump_171
                      apply False.elim assump_124
    case inr assump_5 =>
      cases assump_3
      case intro assump_130 assump_131 =>
        cases assump_130
        case intro assump_132 assump_133 =>
          cases assump_131
          case intro assump_138 assump_139 =>
            cases assump_138
            case inl assump_140 =>
              cases assump_139
              case intro assump_144 assump_145 =>
                have assump_172 : True := by
                  apply True.intro
                let assump_150 := assump_145 assump_172
                apply False.elim assump_150
            case inr assump_141 =>
              cases assump_139
              case intro assump_156 assump_157 =>
                have assump_173 : True := by
                  apply True.intro
                let assump_162 := assump_157 assump_173
                apply False.elim assump_162


variable (p2 p4 p0 p1 p5 p6 p7 p3 : Prop)
theorem file58_61491 : (((((False → False) → False) → ((p3 ∧ p7) ∧ (p4 → True))) → (((p1 ∧ p3) ∧ (False → False)) → ((p3 ∨ False) → (p6 ∧ p5)))) → ((((p7 → p4) → (p2 ∨ True)) ∨ ((p2 ∧ p7) ∧ (p7 → p6))) ∨ (((True ∧ p5) → (p0 ∨ True)) → ((p4 ∨ True) → (p7 ∨ p5))))) := by
  intro assump_10
  apply Or.inl
  apply Or.inl
  intro assump_13
  apply Or.inr
  apply True.intro


variable (p0 p2 p3 p6 p4 p7 : Prop)
theorem file58_61898 : (((((p4 ∧ p3) ∨ (p4 ∨ p4)) ∧ ((p4 ∧ p4) → False)) → False) ∨ ((((p2 → False) ∨ (p2 ∧ p0)) ∨ ((p3 → True) → False)) ∧ (((p6 → True) ∨ (p7 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_36 : (p4 ∧ p4) := by
          apply And.intro
          exact assump_6
          exact assump_6
        let assump_14 := assump_3 assump_36
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_18 =>
        have assump_37 : (p4 ∧ p4) := by
          apply And.intro
          exact assump_18
          exact assump_18
        let assump_24 := assump_3 assump_37
        apply False.elim assump_24
      case inr assump_19 =>
        have assump_38 : (p4 ∧ p4) := by
          apply And.intro
          exact assump_19
          exact assump_19
        let assump_32 := assump_3 assump_38
        apply False.elim assump_32


variable (p5 p2 p0 p3 p6 p7 p1 : Prop)
theorem file58_63005 : ((((((False ∧ p0) ∨ (p3 ∨ p2)) → ((p0 → p3) → False)) ∧ (((p5 → False) ∧ (p0 ∧ p3)) ∧ ((p7 ∧ p6) ∨ (p1 ∧ p2)))) ∧ ((((p3 ∨ p0) ∧ (p0 ∧ False)) ∧ ((p6 ∨ p6) ∧ (p7 → p6))) ∧ (((p0 → p3) ∨ (True ∨ p2)) → ((p2 ∨ p7) ∧ (p2 → p3))))) → False) := by
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
            cases assump_9
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_3
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case inl assump_34 =>
                        cases assump_33
                        case intro assump_38 assump_39 =>
                          apply False.elim assump_39
                      case inr assump_35 =>
                        cases assump_33
                        case intro assump_46 assump_47 =>
                          apply False.elim assump_47
            case inr assump_21 =>
              cases assump_21
              case intro assump_52 assump_53 =>
                cases assump_3
                case intro assump_58 assump_59 =>
                  cases assump_58
                  case intro assump_60 assump_61 =>
                    cases assump_60
                    case intro assump_62 assump_63 =>
                      cases assump_62
                      case inl assump_64 =>
                        cases assump_63
                        case intro assump_68 assump_69 =>
                          apply False.elim assump_69
                      case inr assump_65 =>
                        cases assump_63
                        case intro assump_76 assump_77 =>
                          apply False.elim assump_77


variable (p6 p2 p0 p7 p1 : Prop)
theorem file58_65243 : ((((((p1 ∧ p2) ∧ (p2 ∨ p6)) → ((False ∨ False) ∨ (p2 → False))) → False) ∧ ((((p0 ∧ p0) → False) → ((p7 ∧ True) → (p0 → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p0 ∧ p0) → False) → ((p7 ∧ True) → (p0 → p0))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        exact assump_11
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p0 p5 p3 p1 p4 p7 p2 : Prop)
theorem file58_65822 : (((((False ∨ True) ∧ (False ∧ p7)) ∧ ((p5 ∨ p1) → (False → True))) ∧ (((p2 ∨ p5) → (p0 → False)) → ((False ∨ p4) → (p2 ∨ False)))) → ((((p2 ∧ p5) ∨ (False → False)) → False) → (((p5 → p1) → False) ∧ ((p0 → p3) → False)))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  intro assump_7
  cases assump_5
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          apply False.elim assump_18
        case inr assump_19 =>
          cases assump_17
          case intro assump_24 assump_25 =>
            apply False.elim assump_24
  intro assump_28
  cases assump_5
  case intro assump_33 assump_34 =>
    cases assump_33
    case intro assump_35 assump_36 =>
      cases assump_35
      case intro assump_37 assump_38 =>
        cases assump_37
        case inl assump_39 =>
          apply False.elim assump_39
        case inr assump_40 =>
          cases assump_38
          case intro assump_45 assump_46 =>
            apply False.elim assump_45


variable (p6 p7 p3 p0 p5 p4 p1 : Prop)
theorem file58_67006 : ((((((p7 ∨ p3) ∨ (p3 → False)) ∨ ((p5 → p6) → False)) → (((p3 → False) → False) ∨ ((True ∧ False) ∧ (p7 → False)))) ∧ ((((p1 ∧ p4) ∨ (p4 ∧ p4)) ∨ ((p4 ∧ False) ∨ (True → False))) ∧ (((p5 ∧ p4) → (p1 → p0)) ∧ ((p4 ∨ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              have assump_66 : (p4 ∨ p7) := by
                apply Or.inl
                exact assump_13
              let assump_24 := assump_19 assump_66
              apply False.elim assump_24
        case inr assump_11 =>
          cases assump_11
          case intro assump_28 assump_29 =>
            cases assump_7
            case intro assump_34 assump_35 =>
              have assump_67 : (p4 ∨ p7) := by
                apply Or.inl
                exact assump_29
              let assump_40 := assump_35 assump_67
              apply False.elim assump_40
      case inr assump_9 =>
        cases assump_9
        case inl assump_44 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            apply False.elim assump_47
        case inr assump_45 =>
          cases assump_7
          case intro assump_54 assump_55 =>
            have assump_68 : True := by
              apply True.intro
            let assump_62 := assump_45 assump_68
            apply False.elim assump_62


variable (p2 p5 p3 p0 p4 p1 p7 : Prop)
theorem file58_68702 : ((((((p3 → True) ∨ (p5 ∨ p5)) ∨ ((p1 ∨ p0) ∨ (p7 ∧ p2))) ∨ (((p2 → p7) → (p3 → p4)) → False)) → False) → False) := by
  intro assump_5
  have assump_13 : ((((p3 → True) ∨ (p5 ∨ p5)) ∨ ((p1 ∨ p0) ∨ (p7 ∧ p2))) ∨ (((p2 → p7) → (p3 → p4)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_9
    apply True.intro
  let assump_8 := assump_5 assump_13
  apply False.elim assump_8


variable (p5 p7 p2 p3 p4 p1 : Prop)
theorem file58_69170 : (((((True → p7) → (p5 → False)) → False) ∧ (((p7 → p7) → (p2 → p2)) ∧ ((p4 ∨ True) ∨ (p3 ∧ p5)))) → ((((p7 → p7) ∨ (p7 → p2)) → False) → (((False ∨ p3) ∧ (p5 ∨ p1)) ∨ ((p3 ∧ p4) → (True ∨ False))))) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_10
    case intro assump_13 assump_14 =>
      cases assump_14
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          apply Or.inr
          intro assump_23
          cases assump_23
          case intro assump_24 assump_25 =>
            apply Or.inl
            apply True.intro
        case inr assump_20 =>
          apply Or.inr
          intro assump_32
          cases assump_32
          case intro assump_33 assump_34 =>
            apply Or.inl
            apply True.intro
      case inr assump_18 =>
        cases assump_18
        case intro assump_39 assump_40 =>
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_39
          apply Or.inl
          exact assump_40


variable (p2 p3 p0 p4 p7 p6 p5 : Prop)
theorem file58_70303 : (((((p3 → p3) → False) → False) ∨ (((p6 → False) → (p2 → False)) → False)) ∨ ((((p7 ∨ p4) ∧ (p5 → p0)) → ((p2 ∨ p3) ∧ (p2 → p0))) ∨ (((p5 → False) → False) ∧ ((p2 → False) → (False ∧ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  have assump_19 : (p3 → p3) := by
    intro assump_13
    exact assump_13
  let assump_12 := assump_9 assump_19
  apply False.elim assump_12


variable (p0 p3 p1 p2 p5 p7 p6 p4 : Prop)
theorem file58_70755 : (((((p2 ∨ True) → False) ∧ ((p4 ∨ p2) ∧ (p2 ∧ False))) ∧ (((p4 ∨ p0) → False) ∨ ((p5 ∧ p5) ∧ (p1 → False)))) → ((((p2 ∨ p7) ∧ (p3 ∧ p6)) ∨ ((False ∨ p1) → (p0 ∧ p2))) → False)) := by
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
          cases assump_1
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_20
              case intro assump_23 assump_24 =>
                cases assump_23
                case inl assump_25 =>
                  cases assump_24
                  case intro assump_29 assump_30 =>
                    apply False.elim assump_30
                case inr assump_26 =>
                  cases assump_24
                  case intro assump_37 assump_38 =>
                    apply False.elim assump_38
      case inr assump_8 =>
        cases assump_6
        case intro assump_45 assump_46 =>
          cases assump_1
          case intro assump_51 assump_52 =>
            cases assump_51
            case intro assump_53 assump_54 =>
              cases assump_54
              case intro assump_57 assump_58 =>
                cases assump_57
                case inl assump_59 =>
                  cases assump_58
                  case intro assump_63 assump_64 =>
                    apply False.elim assump_64
                case inr assump_60 =>
                  cases assump_58
                  case intro assump_71 assump_72 =>
                    apply False.elim assump_72
  case inr assump_4 =>
    cases assump_1
    case intro assump_79 assump_80 =>
      cases assump_79
      case intro assump_81 assump_82 =>
        cases assump_82
        case intro assump_85 assump_86 =>
          cases assump_85
          case inl assump_87 =>
            cases assump_86
            case intro assump_91 assump_92 =>
              apply False.elim assump_92
          case inr assump_88 =>
            cases assump_86
            case intro assump_99 assump_100 =>
              apply False.elim assump_100


variable (p1 p2 p5 p0 p6 p7 p4 p3 : Prop)
theorem file58_73058 : (((((p6 → p6) → (p1 → False)) → ((p3 → p0) ∧ (p3 ∨ True))) ∧ (((True → False) → (p5 ∧ True)) → False)) → ((((p7 → False) ∨ (p6 ∨ p7)) ∨ ((False ∧ p7) → False)) ∨ (((p3 ∧ p4) → False) ∨ ((p3 ∨ p2) ∧ (p7 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_23 : ((True → False) → (p5 ∧ True)) := by
      intro assump_13
      apply And.intro
      have assump_24 : True := by
        apply True.intro
      let assump_16 := assump_13 assump_24
      apply False.elim assump_16
      apply True.intro
    let assump_12 := assump_3 assump_23
    apply False.elim assump_12


variable (p3 p7 p6 p1 p2 p5 p0 : Prop)
theorem file58_73811 : (((((p0 ∨ p7) ∨ (p6 → p3)) → False) ∧ (((p6 ∧ True) ∨ (p2 ∧ p3)) ∨ ((p3 ∨ p1) → (p1 ∨ p6)))) → ((((False → p0) ∧ (p3 ∧ p5)) → ((p5 → False) ∨ (p7 ∧ False))) → (((p3 ∨ True) ∧ (False → False)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply Or.inl
          apply And.intro
          apply Or.inr
          apply True.intro
          intro assump_19
          apply False.elim assump_19
      case inr assump_12 =>
        cases assump_12
        case intro assump_22 assump_23 =>
          apply Or.inl
          apply And.intro
          apply Or.inl
          exact assump_23
          intro assump_28
          apply False.elim assump_28
    case inr assump_10 =>
      apply Or.inl
      apply And.intro
      apply Or.inr
      apply True.intro
      intro assump_33
      apply False.elim assump_33


variable (p4 p7 p2 p6 p3 p0 : Prop)
theorem file58_74922 : (((((p2 ∧ p2) ∧ (True → False)) ∧ ((p3 ∨ p3) ∧ (True ∨ p4))) → (((p4 → False) ∨ (p4 ∧ p6)) ∨ ((p3 ∧ True) → False))) ∨ ((((p7 → False) → False) ∨ ((p2 → False) → False)) ∨ (((p7 → False) ∨ (p0 → p2)) → False))) := by
  apply Or.inl
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_21
        case intro assump_32 assump_33 =>
          cases assump_32
          case inl assump_34 =>
            cases assump_33
            case inl assump_38 =>
              apply Or.inl
              apply Or.inl
              intro assump_42
              have assump_90 : True := by
                apply True.intro
              let assump_47 := assump_23 assump_90
              apply False.elim assump_47
            case inr assump_39 =>
              apply Or.inl
              apply Or.inl
              intro assump_53
              have assump_91 : True := by
                apply True.intro
              let assump_59 := assump_23 assump_91
              apply False.elim assump_59
          case inr assump_35 =>
            cases assump_33
            case inl assump_65 =>
              apply Or.inl
              apply Or.inl
              intro assump_69
              have assump_92 : True := by
                apply True.intro
              let assump_74 := assump_23 assump_92
              apply False.elim assump_74
            case inr assump_66 =>
              apply Or.inl
              apply Or.inl
              intro assump_80
              have assump_93 : True := by
                apply True.intro
              let assump_86 := assump_23 assump_93
              apply False.elim assump_86


variable (p7 p2 p4 p5 p1 p3 p6 : Prop)
theorem file58_76761 : (((((p5 → False) ∨ (p4 ∨ p1)) ∨ ((p1 → False) → False)) → False) → ((((p6 ∧ False) → False) → ((p1 → p7) ∧ (p2 ∧ p3))) → (((p4 → p2) → (False → p6)) ∧ ((True ∨ p1) ∨ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p2 p5 p1 p0 p7 p3 p4 : Prop)
theorem file58_77176 : (((((p1 → True) → False) → ((False → p3) → (p4 ∨ True))) ∨ (((p0 ∨ p5) ∨ (p7 ∨ p4)) ∧ ((p7 ∨ p1) → False))) ∧ ((((p0 ∨ p4) ∨ (p0 ∧ p4)) ∨ ((p2 ∧ p7) → (False → p4))) ∨ (((p2 → False) ∨ (p3 ∧ p1)) → ((False → False) ∧ (p5 ∨ p7))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  apply True.intro
  apply Or.inl
  apply Or.inr
  intro assump_7
  intro assump_8
  apply False.elim assump_8


variable (p0 p3 p1 p7 p6 : Prop)
theorem file58_77663 : (((((p7 ∨ p0) ∧ (p6 → False)) → ((p6 → p0) → False)) ∨ (((p0 → False) → False) → ((p1 ∧ p7) → False))) → ((((p6 ∨ p3) → False) → False) → (((p0 ∧ p1) → False) → ((False → p6) ∨ (p0 ∨ False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  case inr assump_9 =>
    apply Or.inl
    intro assump_17
    apply False.elim assump_17


variable (p0 p7 p3 p2 p5 p1 p6 : Prop)
theorem file58_78176 : ((((((p0 → p5) → (p5 → False)) → ((p5 → False) ∧ (p7 → False))) ∨ (((True → p1) ∧ (p5 → p5)) → False)) ∧ ((((p5 ∨ False) → (p0 ∧ p7)) → ((p6 → False) ∧ (p7 → p5))) ∧ (((p2 ∧ p7) → (p3 ∨ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_44 : ((p2 ∧ p7) → (p3 ∨ p7)) := by
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply Or.inr
            exact assump_17
        let assump_14 := assump_9 assump_44
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_3
      case intro assump_27 assump_28 =>
        have assump_45 : ((p2 ∧ p7) → (p3 ∨ p7)) := by
          intro assump_34
          cases assump_34
          case intro assump_35 assump_36 =>
            apply Or.inr
            exact assump_36
        let assump_33 := assump_28 assump_45
        apply False.elim assump_33


variable (p3 p6 p5 p7 p2 : Prop)
theorem file58_79274 : ((((((p5 → False) → (p7 ∨ p2)) → False) → (((p6 → False) ∧ (p5 ∧ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p5 → False) → (p7 ∨ p2)) → False) → (((p6 → False) ∧ (p5 ∧ p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_34 : ((p5 → False) → (p7 ∨ p2)) := by
          intro assump_20
          have assump_35 : p5 := by
            exact assump_11
          let assump_23 := assump_20 assump_35
          apply False.elim assump_23
        let assump_19 := assump_5 assump_34
        apply False.elim assump_19
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p1 p4 p7 p5 p3 : Prop)
theorem file58_80085 : ((((((p1 → False) ∧ (p1 ∧ p5)) → False) ∨ (((p4 ∧ True) ∨ (p4 → p7)) → ((p5 ∧ p3) ∨ (p3 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p1 → False) ∧ (p1 ∧ p5)) → False) ∨ (((p4 ∧ True) ∨ (p4 → p7)) → ((p5 ∧ p3) ∨ (p3 ∨ p1)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : p1 := by
          exact assump_10
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p3 p6 p5 p7 p0 : Prop)
theorem file58_80759 : (((((p0 ∧ p7) ∧ (p2 ∧ p7)) → False) → (((True → False) → (p3 → False)) ∨ ((p2 ∨ p5) ∧ (p0 → False)))) ∧ ((((p2 → False) → (True → True)) → False) → (((False → False) ∨ (p6 ∨ p7)) → False))) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_50 : True := by
    apply True.intro
  let assump_10 := assump_4 assump_50
  apply False.elim assump_10
  intro assump_14
  intro assump_15
  cases assump_15
  case inl assump_16 =>
    have assump_51 : ((p2 → False) → (True → True)) := by
      intro assump_23
      intro assump_24
      apply True.intro
    let assump_22 := assump_14 assump_51
    apply False.elim assump_22
  case inr assump_17 =>
    cases assump_17
    case inl assump_28 =>
      have assump_52 : ((p2 → False) → (True → True)) := by
        intro assump_35
        intro assump_36
        apply True.intro
      let assump_34 := assump_14 assump_52
      apply False.elim assump_34
    case inr assump_29 =>
      have assump_53 : ((p2 → False) → (True → True)) := by
        intro assump_45
        intro assump_46
        apply True.intro
      let assump_44 := assump_14 assump_53
      apply False.elim assump_44


variable (p7 p6 p3 p4 p1 p0 : Prop)
theorem file58_82006 : (((((p7 → p7) → (False → False)) → ((p4 ∧ p1) → (False → False))) → False) → ((((p6 → p7) ∨ (p0 → p1)) ∧ ((p1 → p7) → False)) ∧ (((p3 → False) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_45 : (((p7 → p7) → (False → False)) → ((p4 ∧ p1) → (False → False))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    apply False.elim assump_11
  let assump_8 := assump_1 assump_45
  apply False.elim assump_8
  intro assump_17
  have assump_46 : (((p7 → p7) → (False → False)) → ((p4 ∧ p1) → (False → False))) := by
    intro assump_23
    intro assump_24
    intro assump_25
    apply False.elim assump_25
  let assump_22 := assump_1 assump_46
  apply False.elim assump_22
  intro assump_31
  have assump_47 : (((p7 → p7) → (False → False)) → ((p4 ∧ p1) → (False → False))) := by
    intro assump_37
    intro assump_38
    intro assump_39
    apply False.elim assump_39
  let assump_36 := assump_1 assump_47
  apply False.elim assump_36


variable (p3 p1 p7 p4 p5 p0 p2 p6 : Prop)
theorem file58_83100 : (((((p1 → p2) ∧ (p5 → False)) → ((True → False) → (p6 ∧ p4))) → False) → ((((p3 ∨ p6) ∧ (p0 → p4)) ∧ ((p5 → p6) ∧ (p1 ∧ p2))) ∨ (((p7 ∧ p4) → False) ∨ ((p6 ∧ p1) ∧ (False ∧ p4))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_41 : (((p1 → p2) ∧ (p5 → False)) → ((True → False) → (p6 ∧ p4))) := by
      intro assump_14
      intro assump_15
      apply And.intro
      cases assump_14
      case intro assump_18 assump_19 =>
        have assump_42 : True := by
          apply True.intro
        let assump_26 := assump_15 assump_42
        apply False.elim assump_26
      cases assump_14
      case intro assump_32 assump_33 =>
        exact assump_6
    let assump_13 := assump_1 assump_41
    apply False.elim assump_13


variable (p1 p0 p4 p6 p5 p3 p2 : Prop)
theorem file58_83979 : (((((p5 ∧ p1) → False) ∧ ((False → False) → False)) ∧ (((p0 ∨ p6) ∧ (p4 → True)) → ((p0 → False) → (p4 ∨ False)))) → ((((True → p1) ∧ (True ∨ p3)) ∨ ((p5 ∨ p4) ∨ (p2 ∨ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            have assump_137 : (False → False) := by
              intro assump_25
              apply False.elim assump_25
            let assump_24 := assump_16 assump_137
            apply False.elim assump_24
      case inr assump_10 =>
        cases assump_1
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            have assump_138 : (False → False) := by
              intro assump_45
              apply False.elim assump_45
            let assump_44 := assump_36 assump_138
            apply False.elim assump_44
  case inr assump_4 =>
    cases assump_4
    case inl assump_51 =>
      cases assump_51
      case inl assump_53 =>
        cases assump_1
        case intro assump_57 assump_58 =>
          cases assump_57
          case intro assump_59 assump_60 =>
            have assump_139 : (False → False) := by
              intro assump_69
              apply False.elim assump_69
            let assump_68 := assump_60 assump_139
            apply False.elim assump_68
      case inr assump_54 =>
        cases assump_1
        case intro assump_77 assump_78 =>
          cases assump_77
          case intro assump_79 assump_80 =>
            have assump_140 : (False → False) := by
              intro assump_89
              apply False.elim assump_89
            let assump_88 := assump_80 assump_140
            apply False.elim assump_88
    case inr assump_52 =>
      cases assump_52
      case inl assump_95 =>
        cases assump_1
        case intro assump_99 assump_100 =>
          cases assump_99
          case intro assump_101 assump_102 =>
            have assump_141 : (False → False) := by
              intro assump_111
              apply False.elim assump_111
            let assump_110 := assump_102 assump_141
            apply False.elim assump_110
      case inr assump_96 =>
        cases assump_1
        case intro assump_119 assump_120 =>
          cases assump_119
          case intro assump_121 assump_122 =>
            have assump_142 : (False → False) := by
              intro assump_131
              apply False.elim assump_131
            let assump_130 := assump_122 assump_142
            apply False.elim assump_130


variable (p0 p4 p6 p7 : Prop)
theorem file58_86780 : ((((((False → p7) → False) ∨ ((False → True) → False)) → (((False ∨ p6) → (p4 ∨ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : ((((False → p7) → False) ∨ ((False → True) → False)) → (((False ∨ p6) → (p4 ∨ p0)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      have assump_31 : (False → p7) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_9 assump_31
      apply False.elim assump_13
    case inr assump_10 =>
      have assump_32 : (False → True) := by
        intro assump_23
        apply True.intro
      let assump_22 := assump_10 assump_32
      apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p4 p2 p1 p6 p3 p0 : Prop)
theorem file58_87612 : (((((p4 ∧ p2) ∨ (p1 ∧ p4)) ∧ ((False ∧ p4) ∧ (False ∨ p6))) → (((p3 → True) → False) → False)) ∨ ((((p1 → False) → (p0 → False)) ∨ ((p3 ∨ p0) ∧ (p4 ∧ p6))) → (((p1 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
    case inr assump_8 =>
      cases assump_8
      case intro assump_21 assump_22 =>
        cases assump_6
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply False.elim assump_29


variable (p6 p2 p3 p5 p0 p4 p1 : Prop)
theorem file58_88512 : ((((((True → False) → False) → False) ∧ (((p1 ∨ p6) ∨ (p3 → False)) ∧ ((p2 ∨ p0) ∧ (p5 ∨ p3)))) ∧ ((((p4 ∨ p2) ∧ (False → False)) → ((True → False) ∧ (p4 ∨ p6))) ∧ (((False → p0) ∧ (p3 ∨ p1)) ∧ ((p3 ∧ p4) → False)))) → False) := by
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
          case inl assump_12 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_17
                case inl assump_22 =>
                  cases assump_3
                  case intro assump_26 assump_27 =>
                    cases assump_27
                    case intro assump_30 assump_31 =>
                      cases assump_30
                      case intro assump_32 assump_33 =>
                        cases assump_33
                        case inl assump_36 =>
                          have assump_656 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_18
                            intro assump_46
                            apply False.elim assump_46
                          let assump_45 := assump_26 assump_656
                          let assump_49 := And.left assump_45
                          have assump_657 : True := by
                            apply True.intro
                          let assump_50 := assump_49 assump_657
                          apply False.elim assump_50
                        case inr assump_37 =>
                          have assump_658 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_18
                            intro assump_62
                            apply False.elim assump_62
                          let assump_61 := assump_26 assump_658
                          let assump_65 := And.left assump_61
                          have assump_659 : True := by
                            apply True.intro
                          let assump_66 := assump_65 assump_659
                          apply False.elim assump_66
                case inr assump_23 =>
                  cases assump_3
                  case intro assump_72 assump_73 =>
                    cases assump_73
                    case intro assump_76 assump_77 =>
                      cases assump_76
                      case intro assump_78 assump_79 =>
                        cases assump_79
                        case inl assump_82 =>
                          have assump_660 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_18
                            intro assump_92
                            apply False.elim assump_92
                          let assump_91 := assump_72 assump_660
                          let assump_95 := And.left assump_91
                          have assump_661 : True := by
                            apply True.intro
                          let assump_96 := assump_95 assump_661
                          apply False.elim assump_96
                        case inr assump_83 =>
                          have assump_662 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_18
                            intro assump_108
                            apply False.elim assump_108
                          let assump_107 := assump_72 assump_662
                          let assump_111 := And.left assump_107
                          have assump_663 : True := by
                            apply True.intro
                          let assump_112 := assump_111 assump_663
                          apply False.elim assump_112
              case inr assump_19 =>
                cases assump_17
                case inl assump_118 =>
                  cases assump_3
                  case intro assump_122 assump_123 =>
                    cases assump_123
                    case intro assump_126 assump_127 =>
                      cases assump_126
                      case intro assump_128 assump_129 =>
                        cases assump_129
                        case inl assump_132 =>
                          have assump_664 : ((True → False) → False) := by
                            intro assump_146
                            have assump_665 : True := by
                              apply True.intro
                            let assump_149 := assump_146 assump_665
                            apply False.elim assump_149
                          let assump_145 := assump_4 assump_664
                          apply False.elim assump_145
                        case inr assump_133 =>
                          have assump_666 : ((True → False) → False) := by
                            intro assump_168
                            have assump_667 : True := by
                              apply True.intro
                            let assump_171 := assump_168 assump_667
                            apply False.elim assump_171
                          let assump_167 := assump_4 assump_666
                          apply False.elim assump_167
                case inr assump_119 =>
                  cases assump_3
                  case intro assump_180 assump_181 =>
                    cases assump_181
                    case intro assump_184 assump_185 =>
                      cases assump_184
                      case intro assump_186 assump_187 =>
                        cases assump_187
                        case inl assump_190 =>
                          have assump_668 : ((True → False) → False) := by
                            intro assump_204
                            have assump_669 : True := by
                              apply True.intro
                            let assump_207 := assump_204 assump_669
                            apply False.elim assump_207
                          let assump_203 := assump_4 assump_668
                          apply False.elim assump_203
                        case inr assump_191 =>
                          have assump_670 : ((True → False) → False) := by
                            intro assump_226
                            have assump_671 : True := by
                              apply True.intro
                            let assump_229 := assump_226 assump_671
                            apply False.elim assump_229
                          let assump_225 := assump_4 assump_670
                          apply False.elim assump_225
          case inr assump_13 =>
            cases assump_9
            case intro assump_238 assump_239 =>
              cases assump_238
              case inl assump_240 =>
                cases assump_239
                case inl assump_244 =>
                  cases assump_3
                  case intro assump_248 assump_249 =>
                    cases assump_249
                    case intro assump_252 assump_253 =>
                      cases assump_252
                      case intro assump_254 assump_255 =>
                        cases assump_255
                        case inl assump_258 =>
                          have assump_672 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_240
                            intro assump_268
                            apply False.elim assump_268
                          let assump_267 := assump_248 assump_672
                          let assump_271 := And.left assump_267
                          have assump_673 : True := by
                            apply True.intro
                          let assump_272 := assump_271 assump_673
                          apply False.elim assump_272
                        case inr assump_259 =>
                          have assump_674 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_240
                            intro assump_284
                            apply False.elim assump_284
                          let assump_283 := assump_248 assump_674
                          let assump_287 := And.left assump_283
                          have assump_675 : True := by
                            apply True.intro
                          let assump_288 := assump_287 assump_675
                          apply False.elim assump_288
                case inr assump_245 =>
                  cases assump_3
                  case intro assump_294 assump_295 =>
                    cases assump_295
                    case intro assump_298 assump_299 =>
                      cases assump_298
                      case intro assump_300 assump_301 =>
                        cases assump_301
                        case inl assump_304 =>
                          have assump_676 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_240
                            intro assump_314
                            apply False.elim assump_314
                          let assump_313 := assump_294 assump_676
                          let assump_317 := And.left assump_313
                          have assump_677 : True := by
                            apply True.intro
                          let assump_318 := assump_317 assump_677
                          apply False.elim assump_318
                        case inr assump_305 =>
                          have assump_678 : ((p4 ∨ p2) ∧ (False → False)) := by
                            apply And.intro
                            apply Or.inr
                            exact assump_240
                            intro assump_330
                            apply False.elim assump_330
                          let assump_329 := assump_294 assump_678
                          let assump_333 := And.left assump_329
                          have assump_679 : True := by
                            apply True.intro
                          let assump_334 := assump_333 assump_679
                          apply False.elim assump_334
              case inr assump_241 =>
                cases assump_239
                case inl assump_340 =>
                  cases assump_3
                  case intro assump_344 assump_345 =>
                    cases assump_345
                    case intro assump_348 assump_349 =>
                      cases assump_348
                      case intro assump_350 assump_351 =>
                        cases assump_351
                        case inl assump_354 =>
                          have assump_680 : ((True → False) → False) := by
                            intro assump_368
                            have assump_681 : True := by
                              apply True.intro
                            let assump_371 := assump_368 assump_681
                            apply False.elim assump_371
                          let assump_367 := assump_4 assump_680
                          apply False.elim assump_367
                        case inr assump_355 =>
                          have assump_682 : ((True → False) → False) := by
                            intro assump_390
                            have assump_683 : True := by
                              apply True.intro
                            let assump_393 := assump_390 assump_683
                            apply False.elim assump_393
                          let assump_389 := assump_4 assump_682
                          apply False.elim assump_389
                case inr assump_341 =>
                  cases assump_3
                  case intro assump_402 assump_403 =>
                    cases assump_403
                    case intro assump_406 assump_407 =>
                      cases assump_406
                      case intro assump_408 assump_409 =>
                        cases assump_409
                        case inl assump_412 =>
                          have assump_684 : ((True → False) → False) := by
                            intro assump_426
                            have assump_685 : True := by
                              apply True.intro
                            let assump_429 := assump_426 assump_685
                            apply False.elim assump_429
                          let assump_425 := assump_4 assump_684
                          apply False.elim assump_425
                        case inr assump_413 =>
                          have assump_686 : ((True → False) → False) := by
                            intro assump_448
                            have assump_687 : True := by
                              apply True.intro
                            let assump_451 := assump_448 assump_687
                            apply False.elim assump_451
                          let assump_447 := assump_4 assump_686
                          apply False.elim assump_447
        case inr assump_11 =>
          cases assump_9
          case intro assump_460 assump_461 =>
            cases assump_460
            case inl assump_462 =>
              cases assump_461
              case inl assump_466 =>
                cases assump_3
                case intro assump_470 assump_471 =>
                  cases assump_471
                  case intro assump_474 assump_475 =>
                    cases assump_474
                    case intro assump_476 assump_477 =>
                      cases assump_477
                      case inl assump_480 =>
                        have assump_688 : ((p4 ∨ p2) ∧ (False → False)) := by
                          apply And.intro
                          apply Or.inr
                          exact assump_462
                          intro assump_490
                          apply False.elim assump_490
                        let assump_489 := assump_470 assump_688
                        let assump_493 := And.left assump_489
                        have assump_689 : True := by
                          apply True.intro
                        let assump_494 := assump_493 assump_689
                        apply False.elim assump_494
                      case inr assump_481 =>
                        have assump_690 : ((p4 ∨ p2) ∧ (False → False)) := by
                          apply And.intro
                          apply Or.inr
                          exact assump_462
                          intro assump_506
                          apply False.elim assump_506
                        let assump_505 := assump_470 assump_690
                        let assump_509 := And.left assump_505
                        have assump_691 : True := by
                          apply True.intro
                        let assump_510 := assump_509 assump_691
                        apply False.elim assump_510
              case inr assump_467 =>
                cases assump_3
                case intro assump_516 assump_517 =>
                  cases assump_517
                  case intro assump_520 assump_521 =>
                    cases assump_520
                    case intro assump_522 assump_523 =>
                      cases assump_523
                      case inl assump_526 =>
                        have assump_692 : ((p4 ∨ p2) ∧ (False → False)) := by
                          apply And.intro
                          apply Or.inr
                          exact assump_462
                          intro assump_536
                          apply False.elim assump_536
                        let assump_535 := assump_516 assump_692
                        let assump_539 := And.left assump_535
                        have assump_693 : True := by
                          apply True.intro
                        let assump_540 := assump_539 assump_693
                        apply False.elim assump_540
                      case inr assump_527 =>
                        have assump_694 : ((p4 ∨ p2) ∧ (False → False)) := by
                          apply And.intro
                          apply Or.inr
                          exact assump_462
                          intro assump_552
                          apply False.elim assump_552
                        let assump_551 := assump_516 assump_694
                        let assump_555 := And.left assump_551
                        have assump_695 : True := by
                          apply True.intro
                        let assump_556 := assump_555 assump_695
                        apply False.elim assump_556
            case inr assump_463 =>
              cases assump_461
              case inl assump_562 =>
                cases assump_3
                case intro assump_566 assump_567 =>
                  cases assump_567
                  case intro assump_570 assump_571 =>
                    cases assump_570
                    case intro assump_572 assump_573 =>
                      cases assump_573
                      case inl assump_576 =>
                        have assump_696 : p3 := by
                          exact assump_576
                        let assump_588 := assump_11 assump_696
                        apply False.elim assump_588
                      case inr assump_577 =>
                        have assump_697 : ((True → False) → False) := by
                          intro assump_604
                          have assump_698 : True := by
                            apply True.intro
                          let assump_607 := assump_604 assump_698
                          apply False.elim assump_607
                        let assump_603 := assump_4 assump_697
                        apply False.elim assump_603
              case inr assump_563 =>
                cases assump_3
                case intro assump_616 assump_617 =>
                  cases assump_617
                  case intro assump_620 assump_621 =>
                    cases assump_620
                    case intro assump_622 assump_623 =>
                      cases assump_623
                      case inl assump_626 =>
                        have assump_699 : p3 := by
                          exact assump_626
                        let assump_638 := assump_11 assump_699
                        apply False.elim assump_638
                      case inr assump_627 =>
                        have assump_700 : p3 := by
                          exact assump_563
                        let assump_652 := assump_11 assump_700
                        apply False.elim assump_652


variable (p2 p7 p6 p5 p4 p3 : Prop)
theorem file58_107793 : ((((((p2 ∨ p4) → (True ∨ True)) → ((p2 ∧ p5) → (p6 → False))) ∧ (((False ∨ p5) ∧ (False ∨ p6)) ∧ ((p2 ∨ p2) → False))) ∧ ((((p6 → False) → False) ∨ ((False ∨ p7) → (p3 → False))) → False)) → False) := by
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
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_11
            case inl assump_18 =>
              apply False.elim assump_18
            case inr assump_19 =>
              have assump_39 : (((p6 → False) → False) ∨ ((False ∨ p7) → (p3 → False))) := by
                apply Or.inl
                intro assump_29
                have assump_40 : p6 := by
                  exact assump_19
                let assump_32 := assump_29 assump_40
                apply False.elim assump_32
              let assump_28 := assump_3 assump_39
              apply False.elim assump_28


variable (p4 p5 p0 p3 p6 p7 : Prop)
theorem file58_108988 : ((((((p3 ∨ p5) ∨ (False → p7)) ∨ ((p5 ∨ p0) → False)) ∨ (((p5 → p7) ∧ (p4 ∨ p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 ∨ p5) ∨ (False → p7)) ∨ ((p5 ∨ p0) → False)) ∨ (((p5 → p7) ∧ (p4 ∨ p6)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p6 p3 p0 p2 p7 : Prop)
theorem file58_109459 : (((((p6 ∨ p2) ∧ (True → False)) ∧ ((p5 ∨ p3) ∨ (p5 → False))) → False) ∨ ((((p7 ∧ p5) ∧ (p0 ∧ True)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            have assump_66 : True := by
              apply True.intro
            let assump_19 := assump_5 assump_66
            apply False.elim assump_19
          case inr assump_15 =>
            have assump_67 : True := by
              apply True.intro
            let assump_26 := assump_5 assump_67
            apply False.elim assump_26
        case inr assump_13 =>
          have assump_68 : True := by
            apply True.intro
          let assump_33 := assump_5 assump_68
          apply False.elim assump_33
      case inr assump_7 =>
        cases assump_3
        case inl assump_41 =>
          cases assump_41
          case inl assump_43 =>
            have assump_69 : True := by
              apply True.intro
            let assump_48 := assump_5 assump_69
            apply False.elim assump_48
          case inr assump_44 =>
            have assump_70 : True := by
              apply True.intro
            let assump_55 := assump_5 assump_70
            apply False.elim assump_55
        case inr assump_42 =>
          have assump_71 : True := by
            apply True.intro
          let assump_62 := assump_5 assump_71
          apply False.elim assump_62


variable (p1 p3 p4 p5 : Prop)
theorem file58_111130 : ((((((p1 → True) ∨ (p1 → False)) → ((p3 → False) → (p1 → False))) → (((p4 → False) ∧ (p5 ∨ True)) → ((p1 → p3) → (False → False)))) → False) → False) := by
  intro assump_33
  have assump_46 : ((((p1 → True) ∨ (p1 → False)) → ((p3 → False) → (p1 → False))) → (((p4 → False) ∧ (p5 ∨ True)) → ((p1 → p3) → (False → False)))) := by
    intro assump_37
    intro assump_38
    intro assump_39
    intro assump_40
    apply False.elim assump_40
  let assump_36 := assump_33 assump_46
  apply False.elim assump_36


variable (p7 p6 p0 p5 p1 p4 : Prop)
theorem file58_111698 : ((((((p0 → p6) ∧ (p7 ∧ p7)) ∨ ((p5 ∧ p6) ∨ (p4 → p6))) → (((False → False) ∨ (p7 ∧ p5)) ∧ ((p0 ∨ p1) ∨ (p5 → False)))) ∧ ((((p0 → True) ∨ (p6 → p5)) ∨ ((True → False) → (False → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p0 → True) ∨ (p6 → p5)) ∨ ((True → False) → (False → p0))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p5 p1 p0 p4 p3 p6 : Prop)
theorem file58_112275 : (((((True → False) → False) → ((True → False) → (False ∨ p1))) ∧ (((True ∨ p3) → (p3 → p3)) → False)) → ((((True → p6) → (p1 → p1)) ∧ ((p3 ∧ True) ∨ (p0 → True))) → (((False ∨ p1) ∨ (p6 ∨ p4)) → ((p4 ∨ p5) ∨ (p0 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      apply False.elim assump_6
    case inr assump_7 =>
      cases assump_2
      case intro assump_12 assump_13 =>
        cases assump_13
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_1
            case intro assump_24 assump_25 =>
              have assump_152 : ((True ∨ p3) → (p3 → p3)) := by
                intro assump_31
                intro assump_32
                cases assump_31
                case inl assump_35 =>
                  exact assump_32
                case inr assump_36 =>
                  exact assump_36
              let assump_30 := assump_25 assump_152
              apply False.elim assump_30
        case inr assump_17 =>
          cases assump_1
          case intro assump_46 assump_47 =>
            have assump_153 : ((True ∨ p3) → (p3 → p3)) := by
              intro assump_53
              intro assump_54
              cases assump_53
              case inl assump_57 =>
                exact assump_54
              case inr assump_58 =>
                exact assump_58
            let assump_52 := assump_47 assump_153
            apply False.elim assump_52
  case inr assump_5 =>
    cases assump_5
    case inl assump_66 =>
      cases assump_2
      case intro assump_70 assump_71 =>
        cases assump_71
        case inl assump_74 =>
          cases assump_74
          case intro assump_76 assump_77 =>
            cases assump_1
            case intro assump_82 assump_83 =>
              have assump_154 : ((True ∨ p3) → (p3 → p3)) := by
                intro assump_89
                intro assump_90
                cases assump_89
                case inl assump_93 =>
                  exact assump_90
                case inr assump_94 =>
                  exact assump_94
              let assump_88 := assump_83 assump_154
              apply False.elim assump_88
        case inr assump_75 =>
          cases assump_1
          case intro assump_104 assump_105 =>
            have assump_155 : ((True ∨ p3) → (p3 → p3)) := by
              intro assump_111
              intro assump_112
              cases assump_111
              case inl assump_115 =>
                exact assump_112
              case inr assump_116 =>
                exact assump_116
            let assump_110 := assump_105 assump_155
            apply False.elim assump_110
    case inr assump_67 =>
      cases assump_2
      case intro assump_126 assump_127 =>
        cases assump_127
        case inl assump_130 =>
          cases assump_130
          case intro assump_132 assump_133 =>
            cases assump_1
            case intro assump_138 assump_139 =>
              apply Or.inl
              apply Or.inl
              exact assump_67
        case inr assump_131 =>
          cases assump_1
          case intro assump_146 assump_147 =>
            apply Or.inl
            apply Or.inl
            exact assump_67


variable (p4 p6 p3 p1 p2 p7 p5 : Prop)
theorem file58_115657 : (((((p1 ∧ p2) → (p4 ∨ p5)) → ((False → False) ∨ (p4 → False))) → False) → ((((p3 ∨ p2) ∨ (p7 → False)) → ((p3 → p5) → (True → False))) → (((p7 → False) → False) ∧ ((p6 ∨ p5) → (p1 → True))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  have assump_22 : (((p1 ∧ p2) → (p4 ∨ p5)) → ((False → False) ∨ (p4 → False))) := by
    intro assump_11
    apply Or.inl
    intro assump_14
    apply False.elim assump_14
  let assump_10 := assump_1 assump_22
  apply False.elim assump_10
  intro assump_20
  intro assump_21
  apply True.intro


variable (p0 p3 p4 p1 p7 p5 p2 p6 : Prop)
theorem file58_116286 : ((((((True ∧ p3) ∨ (True → False)) → False) ∨ (((p0 ∨ p6) → (p6 → p6)) → ((True ∧ p1) ∨ (p2 ∧ p1)))) ∧ ((((False ∧ False) ∧ (p4 → False)) ∧ ((p5 → False) → False)) ∧ (((p6 → False) → (p4 ∨ p4)) ∧ ((p0 ∨ p7) → (p4 ∧ False))))) → False) := by
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
            case intro assump_14 assump_15 =>
              apply False.elim assump_14
    case inr assump_5 =>
      cases assump_3
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_26


variable (p1 p6 p0 p4 p7 p3 : Prop)
theorem file58_117345 : ((((((p1 → False) → False) ∨ ((p4 ∨ False) ∧ (p0 ∧ p7))) → False) ∧ ((((p4 ∧ p6) → (False → p7)) ∨ ((p6 → p6) ∨ (True ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p4 ∧ p6) → (False → p7)) ∨ ((p6 → p6) ∨ (True ∨ p3))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p6 p1 p4 p0 : Prop)
theorem file58_117866 : ((((((p4 ∧ p1) → (True ∧ True)) → False) → (((p4 → False) ∧ (p6 → False)) ∧ ((True → True) ∧ (p4 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p4 ∧ p1) → (True ∧ True)) → False) → (((p4 → False) ∧ (p6 → False)) ∧ ((True → True) ∧ (p4 ∧ p0)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    have assump_45 : ((p4 ∧ p1) → (True ∧ True)) := by
      intro assump_12
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_11 := assump_5 assump_45
    apply False.elim assump_11
    intro assump_16
    have assump_46 : ((p4 ∧ p1) → (True ∧ True)) := by
      intro assump_22
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_21 := assump_5 assump_46
    apply False.elim assump_21
    apply And.intro
    intro assump_26
    apply True.intro
    apply And.intro
    have assump_47 : ((p4 ∧ p1) → (True ∧ True)) := by
      intro assump_30
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_29 := assump_5 assump_47
    apply False.elim assump_29
    have assump_48 : ((p4 ∧ p1) → (True ∧ True)) := by
      intro assump_37
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_36 := assump_5 assump_48
    apply False.elim assump_36
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p6 p1 p0 p5 p7 p4 p3 : Prop)
theorem file58_119313 : (((((p1 → p1) → False) → False) ∧ (((p4 ∨ p5) ∨ (False → True)) → ((False ∨ p1) → (p3 → p3)))) ∨ ((((p3 ∨ p5) → (p0 ∨ False)) → False) ∨ (((True ∨ p4) ∧ (p7 ∨ True)) → ((p1 → p7) ∧ (True ∧ p6))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_32 : (p1 → p1) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case inl assump_16 =>
    apply False.elim assump_16
  case inr assump_17 =>
    cases assump_11
    case inl assump_22 =>
      cases assump_22
      case inl assump_24 =>
        exact assump_13
      case inr assump_25 =>
        exact assump_13
    case inr assump_23 =>
      exact assump_13


variable (p6 p3 p7 p0 p2 p5 : Prop)
theorem file58_120135 : (((((p7 ∧ True) ∨ (p6 ∨ p0)) ∧ ((False → False) ∨ (True ∨ p7))) → False) → ((((p5 ∨ False) ∨ (False → p0)) ∧ ((p6 → False) → False)) → (((p3 → False) → False) ∨ ((False ∨ p0) ∨ (p6 → p2))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        apply Or.inl
        intro assump_15
        have assump_65 : (p6 → False) := by
          intro assump_21
          have assump_66 : (((p7 ∧ True) ∨ (p6 ∨ p0)) ∧ ((False → False) ∨ (True ∨ p7))) := by
            apply And.intro
            apply Or.inr
            apply Or.inl
            exact assump_21
            apply Or.inl
            intro assump_27
            apply False.elim assump_27
          let assump_26 := assump_1 assump_66
          apply False.elim assump_26
        let assump_20 := assump_4 assump_65
        apply False.elim assump_20
      case inr assump_8 =>
        apply False.elim assump_8
    case inr assump_6 =>
      apply Or.inl
      intro assump_44
      have assump_67 : (p6 → False) := by
        intro assump_50
        have assump_68 : (((p7 ∧ True) ∨ (p6 ∨ p0)) ∧ ((False → False) ∨ (True ∨ p7))) := by
          apply And.intro
          apply Or.inr
          apply Or.inl
          exact assump_50
          apply Or.inl
          intro assump_56
          apply False.elim assump_56
        let assump_55 := assump_1 assump_68
        apply False.elim assump_55
      let assump_49 := assump_4 assump_67
      apply False.elim assump_49


variable (p6 p3 p1 p4 p7 : Prop)
theorem file58_121760 : ((((((p3 ∨ p1) → (p7 ∧ True)) ∨ ((p6 → p4) → False)) → (((p4 ∧ p3) ∧ (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_41 : ((((p3 ∨ p1) → (p7 ∧ True)) ∨ ((p6 → p4) → False)) → (((p4 ∧ p3) ∧ (p4 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case inl assump_17 =>
          have assump_42 : p4 := by
            exact assump_9
          let assump_25 := assump_8 assump_42
          apply False.elim assump_25
        case inr assump_18 =>
          have assump_43 : (p6 → p4) := by
            intro assump_32
            exact assump_9
          let assump_31 := assump_18 assump_43
          apply False.elim assump_31
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p5 p1 p6 p0 : Prop)
theorem file58_122693 : ((((((False → p6) ∧ (p0 → True)) → False) → (((p1 → p0) ∨ (True → False)) ∨ ((p5 ∨ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → p6) ∧ (p0 → True)) → False) → (((p1 → p0) ∨ (True → False)) ∨ ((p5 ∨ p5) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_24 : ((False → p6) ∧ (p0 → True)) := by
      apply And.intro
      intro assump_13
      apply False.elim assump_13
      intro assump_16
      apply True.intro
    let assump_12 := assump_5 assump_24
    apply False.elim assump_12
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p1 p2 : Prop)
theorem file58_123390 : (((((p5 ∨ True) → False) ∨ ((False → False) → False)) ∨ (((p2 ∧ p1) → (p1 ∧ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      have assump_34 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_8 := assump_4 assump_34
      apply False.elim assump_8
    case inr assump_5 =>
      have assump_35 : (False → False) := by
        intro assump_15
        apply False.elim assump_15
      let assump_14 := assump_5 assump_35
      apply False.elim assump_14
  case inr assump_3 =>
    have assump_36 : ((p2 ∧ p1) → (p1 ∧ True)) := by
      intro assump_24
      apply And.intro
      cases assump_24
      case intro assump_25 assump_26 =>
        exact assump_26
      apply True.intro
    let assump_23 := assump_3 assump_36
    apply False.elim assump_23


variable (p6 p3 p0 : Prop)
theorem file58_124314 : (((((True → False) → False) ∨ ((p6 ∧ p0) ∧ (p6 → p3))) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → False) ∨ ((p6 ∧ p0) ∧ (p6 → p3))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p3 p6 p0 p4 : Prop)
theorem file58_124770 : ((((((p3 ∧ p6) ∧ (p4 → False)) ∧ ((False → False) → False)) → (((p0 ∧ p7) ∨ (p0 ∧ p0)) ∧ ((p7 ∧ p0) ∧ (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_96 : ((((p3 ∧ p6) ∧ (p4 → False)) ∧ ((False → False) → False)) → (((p0 ∧ p7) ∨ (p0 ∧ p0)) ∧ ((p7 ∧ p0) ∧ (p7 → False)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_97 : (False → False) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_7 assump_97
          apply False.elim assump_20
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          have assump_98 : (False → False) := by
            intro assump_42
            apply False.elim assump_42
          let assump_41 := assump_28 assump_98
          apply False.elim assump_41
    cases assump_5
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          have assump_99 : (False → False) := by
            intro assump_63
            apply False.elim assump_63
          let assump_62 := assump_49 assump_99
          apply False.elim assump_62
    intro assump_69
    cases assump_5
    case intro assump_72 assump_73 =>
      cases assump_72
      case intro assump_74 assump_75 =>
        cases assump_74
        case intro assump_76 assump_77 =>
          have assump_100 : (False → False) := by
            intro assump_87
            apply False.elim assump_87
          let assump_86 := assump_73 assump_100
          apply False.elim assump_86
  let assump_4 := assump_1 assump_96
  apply False.elim assump_4


