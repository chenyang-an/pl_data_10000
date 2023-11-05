variable (p4 p0 p6 p7 p5 : Prop)
theorem file56_41 : (((((p7 → False) → (p6 ∧ p7)) → ((p0 ∨ True) ∧ (True ∨ p7))) → False) → ((((False → False) ∨ (False → False)) ∧ ((p5 ∧ p7) → (False ∨ p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      have assump_37 : (((p7 → False) → (p6 ∧ p7)) → ((p0 ∨ True) ∧ (True ∨ p7))) := by
        intro assump_14
        apply And.intro
        apply Or.inr
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_13 := assump_1 assump_37
      apply False.elim assump_13
    case inr assump_6 =>
      have assump_38 : (((p7 → False) → (p6 ∧ p7)) → ((p0 ∨ True) ∧ (True ∨ p7))) := by
        intro assump_29
        apply And.intro
        apply Or.inr
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_28 := assump_1 assump_38
      apply False.elim assump_28


variable (p3 p4 p1 : Prop)
theorem file56_1008 : ((((((p4 ∧ p1) → False) ∨ ((p3 ∨ True) ∨ (p1 → True))) → (((p4 → False) ∧ (p1 ∧ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_59 : ((((p4 ∧ p1) → False) ∨ ((p3 ∨ True) ∨ (p1 → True))) → (((p4 → False) ∧ (p1 ∧ p4)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_5
        case inl assump_17 =>
          have assump_60 : (p4 ∧ p1) := by
            apply And.intro
            exact assump_12
            exact assump_11
          let assump_21 := assump_17 assump_60
          apply False.elim assump_21
        case inr assump_18 =>
          cases assump_18
          case inl assump_25 =>
            cases assump_25
            case inl assump_27 =>
              have assump_61 : p4 := by
                exact assump_12
              let assump_34 := assump_7 assump_61
              apply False.elim assump_34
            case inr assump_28 =>
              have assump_62 : p4 := by
                exact assump_12
              let assump_42 := assump_7 assump_62
              apply False.elim assump_42
          case inr assump_26 =>
            have assump_63 : p4 := by
              exact assump_12
            let assump_52 := assump_7 assump_63
            apply False.elim assump_52
  let assump_4 := assump_1 assump_59
  apply False.elim assump_4


variable (p3 p2 p6 p0 p7 p5 : Prop)
theorem file56_2502 : (((((p5 ∧ p5) ∨ (p7 ∨ True)) ∨ ((False ∨ p2) → (False ∨ p7))) → False) → ((((True ∨ p3) ∨ (p7 ∧ p3)) → ((p5 ∧ False) ∧ (p6 → False))) → (((p0 ∨ p6) → (p3 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_14 : (((p5 ∧ p5) ∨ (p7 ∨ True)) ∨ ((False ∨ p2) → (False ∨ p7))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_10 := assump_1 assump_14
  apply False.elim assump_10


variable (p5 p0 p7 p1 p3 : Prop)
theorem file56_3015 : ((((((p3 → p5) ∧ (p5 → p7)) ∨ ((p3 ∨ p0) ∨ (p3 ∧ p0))) → (((True → False) ∧ (p1 ∧ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_73 : ((((p3 → p5) ∧ (p5 → p7)) ∨ ((p3 ∨ p0) ∨ (p3 ∧ p0))) → (((True → False) ∧ (p1 ∧ p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_5
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            have assump_74 : True := by
              apply True.intro
            let assump_30 := assump_7 assump_74
            apply False.elim assump_30
        case inr assump_18 =>
          cases assump_18
          case inl assump_34 =>
            cases assump_34
            case inl assump_36 =>
              have assump_75 : True := by
                apply True.intro
              let assump_43 := assump_7 assump_75
              apply False.elim assump_43
            case inr assump_37 =>
              have assump_76 : True := by
                apply True.intro
              let assump_52 := assump_7 assump_76
              apply False.elim assump_52
          case inr assump_35 =>
            cases assump_35
            case intro assump_56 assump_57 =>
              have assump_77 : True := by
                apply True.intro
              let assump_66 := assump_7 assump_77
              apply False.elim assump_66
  let assump_4 := assump_1 assump_73
  apply False.elim assump_4


variable (p6 p7 p1 p4 p5 p3 p2 : Prop)
theorem file56_4624 : ((((((p2 ∧ False) → (p2 ∧ True)) ∧ ((p1 → False) → (False → p1))) ∨ (((p3 ∨ p2) → False) → False)) → ((((False ∧ p7) → (p4 ∨ p1)) → False) ∧ (((p2 ∧ p6) ∧ (False → False)) ∧ ((p4 → False) → (p5 ∧ p3))))) → False) := by
  intro assump_1
  have assump_26 : ((((p2 ∧ False) → (p2 ∧ True)) ∧ ((p1 → False) → (False → p1))) ∨ (((p3 ∨ p2) → False) → False)) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
    apply True.intro
    intro assump_12
    intro assump_13
    apply False.elim assump_13
  let assump_4 := assump_1 assump_26
  let assump_16 := And.left assump_4
  have assump_27 : ((False ∧ p7) → (p4 ∨ p1)) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      apply False.elim assump_19
  let assump_17 := assump_16 assump_27
  apply False.elim assump_17


variable (p1 p4 p6 p0 p5 p2 : Prop)
theorem file56_5602 : (((((p4 → False) → (p5 ∨ p0)) ∨ ((True ∨ False) ∨ (p6 ∨ p4))) → False) → ((((p4 ∨ p4) → False) ∨ ((p6 → p6) ∧ (True ∨ p1))) ∨ (((False ∧ p2) → (False → False)) ∨ ((p1 ∧ p6) ∨ (False ∧ p5))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_35 : (((p4 → False) → (p5 ∨ p0)) ∨ ((True ∨ False) ∨ (p6 ∨ p4))) := by
      apply Or.inl
      intro assump_11
      have assump_36 : p4 := by
        exact assump_5
      let assump_14 := assump_11 assump_36
      apply False.elim assump_14
    let assump_10 := assump_1 assump_35
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_37 : (((p4 → False) → (p5 ∨ p0)) ∨ ((True ∨ False) ∨ (p6 ∨ p4))) := by
      apply Or.inl
      intro assump_25
      have assump_38 : p4 := by
        exact assump_6
      let assump_28 := assump_25 assump_38
      apply False.elim assump_28
    let assump_24 := assump_1 assump_37
    apply False.elim assump_24


variable (p2 p0 p4 p5 p3 p1 p6 : Prop)
theorem file56_6650 : (((((False ∧ p4) → False) → False) ∧ (((True ∨ p3) ∧ (p0 → False)) ∨ ((False ∧ p5) → (p1 ∧ p2)))) → ((((True → False) ∨ (p4 → p5)) → False) ∧ (((False → p4) ∨ (False → p6)) ∧ ((False → p4) ∨ (p6 ∧ p2))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            have assump_169 : ((False ∧ p4) → False) := by
              intro assump_23
              cases assump_23
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
            let assump_22 := assump_7 assump_169
            apply False.elim assump_22
          case inr assump_16 =>
            have assump_170 : ((False ∧ p4) → False) := by
              intro assump_38
              cases assump_38
              case intro assump_39 assump_40 =>
                apply False.elim assump_39
            let assump_37 := assump_7 assump_170
            apply False.elim assump_37
      case inr assump_12 =>
        have assump_171 : ((False ∧ p4) → False) := by
          intro assump_50
          cases assump_50
          case intro assump_51 assump_52 =>
            apply False.elim assump_51
        let assump_49 := assump_7 assump_171
        apply False.elim assump_49
  case inr assump_4 =>
    cases assump_1
    case intro assump_60 assump_61 =>
      cases assump_61
      case inl assump_64 =>
        cases assump_64
        case intro assump_66 assump_67 =>
          cases assump_66
          case inl assump_68 =>
            have assump_172 : ((False ∧ p4) → False) := by
              intro assump_76
              cases assump_76
              case intro assump_77 assump_78 =>
                apply False.elim assump_77
            let assump_75 := assump_60 assump_172
            apply False.elim assump_75
          case inr assump_69 =>
            have assump_173 : ((False ∧ p4) → False) := by
              intro assump_91
              cases assump_91
              case intro assump_92 assump_93 =>
                apply False.elim assump_92
            let assump_90 := assump_60 assump_173
            apply False.elim assump_90
      case inr assump_65 =>
        have assump_174 : ((False ∧ p4) → False) := by
          intro assump_103
          cases assump_103
          case intro assump_104 assump_105 =>
            apply False.elim assump_104
        let assump_102 := assump_60 assump_174
        apply False.elim assump_102
  apply And.intro
  cases assump_1
  case intro assump_111 assump_112 =>
    cases assump_112
    case inl assump_115 =>
      cases assump_115
      case intro assump_117 assump_118 =>
        cases assump_117
        case inl assump_119 =>
          apply Or.inl
          intro assump_125
          apply False.elim assump_125
        case inr assump_120 =>
          apply Or.inl
          intro assump_132
          apply False.elim assump_132
    case inr assump_116 =>
      apply Or.inl
      intro assump_137
      apply False.elim assump_137
  cases assump_1
  case intro assump_140 assump_141 =>
    cases assump_141
    case inl assump_144 =>
      cases assump_144
      case intro assump_146 assump_147 =>
        cases assump_146
        case inl assump_148 =>
          apply Or.inl
          intro assump_154
          apply False.elim assump_154
        case inr assump_149 =>
          apply Or.inl
          intro assump_161
          apply False.elim assump_161
    case inr assump_145 =>
      apply Or.inl
      intro assump_166
      apply False.elim assump_166


variable (p3 p1 p7 p6 p0 : Prop)
theorem file56_10440 : ((((((p3 ∨ True) → False) → False) ∨ (((p0 ∧ p1) ∨ (p1 ∨ p6)) ∧ ((p7 → False) ∨ (p3 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p3 ∨ True) → False) → False) ∨ (((p0 ∧ p1) ∨ (p1 ∨ p6)) ∧ ((p7 → False) ∨ (p3 ∨ p0)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p4 p6 p3 p0 p7 : Prop)
theorem file56_11001 : (((((True → False) ∧ (False ∧ True)) → False) ∨ (((p4 ∨ p6) → (p7 → False)) → ((p0 ∨ p5) ∧ (p5 → p3)))) ∨ ((((p5 → False) ∨ (p6 → p3)) → False) ∧ (((p6 → False) → False) → ((False → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6


variable (p7 p2 p3 p0 p6 p1 : Prop)
theorem file56_11453 : (((((p0 → p1) → False) ∧ ((p6 → p0) → (p7 ∧ p0))) ∧ (((False ∨ True) ∧ (False → False)) → False)) → ((((p1 ∧ p1) ∨ (False → False)) → ((p3 → True) ∨ (p2 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_22 : ((False ∨ True) ∧ (False → False)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_6 assump_22
      apply False.elim assump_15


variable (p7 p0 p4 p6 p1 p5 : Prop)
theorem file56_12101 : (((((False ∧ False) → False) → False) → False) ∨ ((((p5 → False) ∨ (p4 → False)) ∧ ((p6 → True) → False)) ∧ (((False ∧ p1) → False) → ((p7 ∧ False) ∨ (True ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p3 p6 p2 p7 p1 p0 p4 : Prop)
theorem file56_12593 : (((((p2 ∨ p6) ∧ (True → False)) → ((p6 ∨ False) ∧ (p7 ∧ p2))) ∨ (((p3 ∧ p1) → False) ∧ ((False ∨ p1) ∧ (p4 → False)))) ∨ ((((p5 ∨ True) → (True → False)) ∧ ((p5 → False) → (p4 ∧ p0))) ∧ (((p0 ∨ False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_54 : True := by
        apply True.intro
      let assump_10 := assump_3 assump_54
      apply False.elim assump_10
    case inr assump_5 =>
      apply Or.inl
      exact assump_5
  apply And.intro
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_18
    case inl assump_20 =>
      have assump_55 : True := by
        apply True.intro
      let assump_26 := assump_19 assump_55
      apply False.elim assump_26
    case inr assump_21 =>
      have assump_56 : True := by
        apply True.intro
      let assump_34 := assump_19 assump_56
      apply False.elim assump_34
  cases assump_1
  case intro assump_38 assump_39 =>
    cases assump_38
    case inl assump_40 =>
      exact assump_40
    case inr assump_41 =>
      have assump_57 : True := by
        apply True.intro
      let assump_50 := assump_39 assump_57
      apply False.elim assump_50


variable (p2 p1 p5 p4 p6 p0 p7 : Prop)
theorem file56_13937 : ((((((p7 ∧ p5) ∨ (p2 ∧ False)) → False) ∧ (((p0 → p4) ∧ (p7 ∧ p2)) ∨ ((p4 → True) → (p1 ∨ p7)))) ∧ ((((p7 ∧ p7) ∨ (True ∧ p6)) ∨ ((p5 ∨ p5) → (p7 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            have assump_56 : (((p7 ∧ p7) ∨ (True ∧ p6)) ∨ ((p5 ∨ p5) → (p7 → False))) := by
              apply Or.inl
              apply Or.inl
              apply And.intro
              exact assump_14
              exact assump_14
            let assump_22 := assump_3 assump_56
            apply False.elim assump_22
      case inr assump_9 =>
        have assump_57 : (((p7 ∧ p7) ∨ (True ∧ p6)) ∨ ((p5 ∨ p5) → (p7 → False))) := by
          apply Or.inr
          intro assump_31
          intro assump_32
          cases assump_31
          case inl assump_35 =>
            have assump_58 : (((p7 ∧ p7) ∨ (True ∧ p6)) ∨ ((p5 ∨ p5) → (p7 → False))) := by
              apply Or.inl
              apply Or.inl
              apply And.intro
              exact assump_32
              exact assump_32
            let assump_41 := assump_3 assump_58
            apply False.elim assump_41
          case inr assump_36 =>
            have assump_59 : (((p7 ∧ p7) ∨ (True ∧ p6)) ∨ ((p5 ∨ p5) → (p7 → False))) := by
              apply Or.inl
              apply Or.inl
              apply And.intro
              exact assump_32
              exact assump_32
            let assump_49 := assump_3 assump_59
            apply False.elim assump_49
        let assump_30 := assump_3 assump_57
        apply False.elim assump_30


variable (p5 p7 p2 p6 p3 p0 p1 : Prop)
theorem file56_15816 : (((((p0 ∨ p0) ∨ (p2 → False)) ∧ ((p1 → False) ∧ (p7 ∨ p3))) → (((True ∧ p1) ∧ (p2 → p2)) ∨ ((p5 → False) → (True ∨ p7)))) ∨ ((((p6 → p0) → False) → False) ∨ (((p7 ∧ True) ∧ (p3 ∨ p1)) ∧ ((p2 → False) ∨ (p6 ∧ p6))))) := by
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
          cases assump_11
          case inl assump_14 =>
            apply Or.inr
            intro assump_18
            apply Or.inl
            apply True.intro
          case inr assump_15 =>
            apply Or.inr
            intro assump_23
            apply Or.inl
            apply True.intro
      case inr assump_7 =>
        cases assump_3
        case intro assump_28 assump_29 =>
          cases assump_29
          case inl assump_32 =>
            apply Or.inr
            intro assump_36
            apply Or.inl
            apply True.intro
          case inr assump_33 =>
            apply Or.inr
            intro assump_41
            apply Or.inl
            apply True.intro
    case inr assump_5 =>
      cases assump_3
      case intro assump_46 assump_47 =>
        cases assump_47
        case inl assump_50 =>
          apply Or.inr
          intro assump_54
          apply Or.inl
          apply True.intro
        case inr assump_51 =>
          apply Or.inr
          intro assump_59
          apply Or.inl
          apply True.intro


variable (p0 p3 p4 p7 p5 p2 p6 p1 : Prop)
theorem file56_17412 : (((((p5 ∨ p6) ∨ (p0 → p5)) → False) ∧ (((p1 ∨ p0) ∧ (p3 ∨ p0)) → False)) → ((((p3 → p4) → (p6 → p7)) ∧ ((p6 ∨ False) → (p1 → True))) ∨ (((p7 → p6) → False) ∧ ((p1 ∧ p2) → (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_8
    intro assump_9
    have assump_23 : ((p5 ∨ p6) ∨ (p0 → p5)) := by
      apply Or.inl
      apply Or.inr
      exact assump_9
    let assump_17 := assump_2 assump_23
    apply False.elim assump_17
    intro assump_21
    intro assump_22
    apply True.intro


variable (p7 p5 p0 p1 p2 p4 p3 p6 : Prop)
theorem file56_18057 : (((((False ∨ p7) → (p7 ∨ p3)) → ((p5 → False) ∧ (True ∨ p0))) ∧ (((True → p6) → (p6 ∨ p3)) ∨ ((p4 → False) → (False → False)))) → ((((p3 ∧ p1) → False) → ((p2 ∧ p3) → (p7 → p2))) ∨ (((p5 ∧ p0) ∧ (p2 ∧ p5)) ∨ ((p6 ∨ p5) ∨ (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      intro assump_12
      cases assump_11
      case intro assump_15 assump_16 =>
        exact assump_15
    case inr assump_7 =>
      apply Or.inl
      intro assump_25
      intro assump_26
      intro assump_27
      cases assump_26
      case intro assump_30 assump_31 =>
        exact assump_30


variable (p6 p0 p7 p5 p4 : Prop)
theorem file56_18837 : ((((((p0 → p0) ∧ (False → p6)) ∧ ((False → p4) ∧ (p7 ∧ p5))) → (((False ∧ p0) → (p0 → p7)) ∨ ((p0 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p0 → p0) ∧ (False → p6)) ∧ ((False → p4) ∧ (p7 ∧ p5))) → (((False ∧ p0) → (p0 → p7)) ∨ ((p0 ∨ p7) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply Or.inl
            intro assump_24
            intro assump_25
            cases assump_24
            case intro assump_28 assump_29 =>
              apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p3 p0 p7 p2 p4 p1 p5 : Prop)
theorem file56_19723 : (((((True → False) → (p0 ∧ True)) ∨ ((p2 ∧ False) → (True → False))) ∨ (((p1 ∧ p0) → False) ∨ ((False ∧ p5) ∧ (p5 ∨ p3)))) ∨ ((((p3 ∧ True) → False) ∧ ((p7 → False) → False)) ∨ (((p4 ∧ True) ∨ (p7 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4
  apply True.intro


variable (p4 p3 p5 p2 p6 p1 p0 p7 : Prop)
theorem file56_20226 : (((((False ∧ p7) ∨ (p6 → True)) ∨ ((p7 ∧ False) → (p2 → False))) ∨ (((False ∧ p7) → (p3 ∧ p7)) ∧ ((p2 ∨ p1) ∨ (True → False)))) ∨ ((((p0 ∧ p6) → (p1 ∧ p2)) → ((p1 ∧ p0) ∧ (p0 → False))) ∨ (((p5 → False) ∨ (p5 ∧ p1)) ∧ ((p5 ∧ p4) ∧ (p3 ∨ p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply True.intro


variable (p3 p0 p2 p1 p5 : Prop)
theorem file56_20630 : ((((((True ∨ p3) ∨ (p1 ∨ True)) → False) ∧ (((p2 ∧ False) ∧ (p1 ∧ p1)) ∧ ((p2 ∨ p0) → False))) ∧ ((((False → False) ∧ (False ∧ True)) → ((p3 ∨ p5) → False)) ∧ (((p0 ∧ p1) → (p2 ∨ p5)) ∧ ((p3 ∧ False) → (p2 → True))))) → False) := by
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
            apply False.elim assump_13


variable (p4 p0 p3 : Prop)
theorem file56_21270 : (((((p0 ∨ p4) → (True ∧ True)) ∧ ((p3 ∨ p0) → False)) ∧ (((p3 ∧ False) → (False ∨ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : ((p3 ∧ False) → (False ∨ p4)) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p5 p0 p4 p1 p2 p6 p7 : Prop)
theorem file56_21829 : (((((False ∧ p6) ∧ (False ∧ p6)) ∨ ((p4 → False) ∧ (True → False))) ∨ (((p5 → p0) → (p2 → False)) ∨ ((p7 ∧ p4) → (True → False)))) → ((((p7 → p1) ∧ (p6 ∧ p0)) ∧ ((p0 → False) ∨ (p7 ∧ False))) → (((p0 ∨ p2) → False) → ((p1 → False) ∨ (p0 ∨ p5))))) := by
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_19
      case intro assump_22 assump_23 =>
        cases assump_17
        case inl assump_28 =>
          cases assump_11
          case inl assump_32 =>
            cases assump_32
            case inl assump_34 =>
              cases assump_34
              case intro assump_36 assump_37 =>
                cases assump_36
                case intro assump_38 assump_39 =>
                  apply False.elim assump_38
            case inr assump_35 =>
              cases assump_35
              case intro assump_42 assump_43 =>
                apply Or.inl
                intro assump_48
                have assump_90 : True := by
                  apply True.intro
                let assump_52 := assump_43 assump_90
                apply False.elim assump_52
          case inr assump_33 =>
            cases assump_33
            case inl assump_56 =>
              apply Or.inl
              intro assump_60
              have assump_91 : p0 := by
                exact assump_23
              let assump_69 := assump_28 assump_91
              apply False.elim assump_69
            case inr assump_57 =>
              apply Or.inl
              intro assump_75
              have assump_92 : p0 := by
                exact assump_23
              let assump_80 := assump_28 assump_92
              apply False.elim assump_80
        case inr assump_29 =>
          cases assump_29
          case intro assump_84 assump_85 =>
            apply False.elim assump_85


variable (p4 p3 p2 : Prop)
theorem file56_23797 : (((((False ∧ p3) → False) ∨ ((p2 ∧ p4) ∨ (True → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((False ∧ p3) → False) ∨ ((p2 ∧ p4) ∨ (True → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p1 p2 p4 : Prop)
theorem file56_24219 : (((((p2 → False) ∧ (p2 ∧ True)) → False) → False) → ((((False ∧ False) ∨ (p6 → p4)) → ((p1 ∨ False) → (p4 → False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_27 : (((p2 → False) ∧ (p2 ∧ True)) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        have assump_28 : p2 := by
          exact assump_13
        let assump_20 := assump_9 assump_28
        apply False.elim assump_20
  let assump_7 := assump_1 assump_27
  apply False.elim assump_7


variable (p6 p2 : Prop)
theorem file56_24839 : ((((((False ∨ p2) ∧ (False ∧ False)) ∨ ((True → False) → False)) ∧ (((False ∧ p6) → False) ∨ ((p6 ∧ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∨ p2) ∧ (False ∧ False)) ∨ ((True → False) → False)) ∧ (((False ∧ p6) → False) ∨ ((p6 ∧ p2) → False))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    have assump_21 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
    apply Or.inl
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p0 p6 p3 p1 p4 p2 p7 p5 : Prop)
theorem file56_25572 : (((((p5 ∧ p7) → False) → ((True → False) → (p6 → p0))) ∧ (((p4 → p6) → (p2 → True)) ∧ ((True → False) → False))) ∨ ((((p2 ∨ True) ∧ (p1 ∨ p3)) → ((p1 → False) ∨ (p7 → False))) → (((p5 → False) → (p5 ∨ False)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_17
  intro assump_18
  intro assump_19
  have assump_40 : True := by
    apply True.intro
  let assump_27 := assump_18 assump_40
  apply False.elim assump_27
  apply And.intro
  intro assump_31
  intro assump_32
  apply True.intro
  intro assump_33
  have assump_41 : True := by
    apply True.intro
  let assump_36 := assump_33 assump_41
  apply False.elim assump_36


variable (p1 p4 p7 p0 p2 : Prop)
theorem file56_26271 : ((((((True ∨ p1) → False) → ((False ∨ p0) ∨ (p4 → False))) ∨ (((p1 ∨ p2) ∧ (False → p4)) ∧ ((p7 ∨ p7) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True ∨ p1) → False) → ((False ∨ p0) ∨ (p4 → False))) ∨ (((p1 ∨ p2) ∧ (False → p4)) ∧ ((p7 ∨ p7) ∨ (False → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_20 : (True ∨ p1) := by
      apply Or.inl
      apply True.intro
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p0 : Prop)
theorem file56_26918 : ((((((False → False) ∨ (p6 ∧ p0)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) ∨ (p6 ∧ p0)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → False) ∨ (p6 ∧ p0)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p7 p6 p0 p3 p4 p2 p5 : Prop)
theorem file56_27434 : (((((p1 ∧ p5) → False) ∧ ((p2 ∨ p2) ∧ (p6 → p7))) → False) → ((((False → False) ∧ (p0 ∨ p5)) → ((p5 → False) → (False ∨ p0))) → (((p2 ∧ p4) → (True ∨ p2)) ∨ ((p7 ∧ False) → (p1 ∨ p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply Or.inl
    apply True.intro


variable (p1 p5 p3 p4 p2 p6 p0 : Prop)
theorem file56_27845 : (((((p5 ∨ True) ∨ (p1 ∧ p2)) ∨ ((p4 ∧ p6) → (p3 → p3))) → False) → ((((p6 ∨ p2) → (p0 ∧ p1)) → ((p6 ∨ p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  have assump_11 : (((p5 ∨ True) ∨ (p1 ∧ p2)) ∨ ((p4 ∧ p6) → (p3 → p3))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p2 p3 p5 : Prop)
theorem file56_28278 : ((((((p5 → True) ∧ (True → False)) → False) ∨ (((False → False) ∨ (p3 → p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p5 → True) ∧ (True → False)) → False) ∨ (((False → False) ∨ (p3 → p2)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p7 p2 p5 p0 p3 : Prop)
theorem file56_28866 : (((((p4 ∨ True) → False) → ((p3 ∨ p0) → (p7 → p3))) → False) → ((((False → False) → False) ∧ ((p2 → False) ∧ (p5 ∨ p4))) ∧ (((False → False) ∨ (p7 ∨ p0)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_169 : (((p4 ∨ True) → False) → ((p3 ∨ p0) → (p7 → p3))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_9
    case inl assump_13 =>
      exact assump_13
    case inr assump_14 =>
      have assump_170 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_23 := assump_8 assump_170
      apply False.elim assump_23
  let assump_7 := assump_1 assump_169
  apply False.elim assump_7
  apply And.intro
  intro assump_30
  have assump_171 : (((p4 ∨ True) → False) → ((p3 ∨ p0) → (p7 → p3))) := by
    intro assump_36
    intro assump_37
    intro assump_38
    cases assump_37
    case inl assump_41 =>
      exact assump_41
    case inr assump_42 =>
      have assump_172 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_51 := assump_36 assump_172
      apply False.elim assump_51
  let assump_35 := assump_1 assump_171
  apply False.elim assump_35
  have assump_173 : (((p4 ∨ True) → False) → ((p3 ∨ p0) → (p7 → p3))) := by
    intro assump_61
    intro assump_62
    intro assump_63
    cases assump_62
    case inl assump_66 =>
      exact assump_66
    case inr assump_67 =>
      have assump_174 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_76 := assump_61 assump_174
      apply False.elim assump_76
  let assump_60 := assump_1 assump_173
  apply False.elim assump_60
  intro assump_83
  cases assump_83
  case inl assump_84 =>
    have assump_175 : (((p4 ∨ True) → False) → ((p3 ∨ p0) → (p7 → p3))) := by
      intro assump_91
      intro assump_92
      intro assump_93
      cases assump_92
      case inl assump_96 =>
        exact assump_96
      case inr assump_97 =>
        have assump_176 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_106 := assump_91 assump_176
        apply False.elim assump_106
    let assump_90 := assump_1 assump_175
    apply False.elim assump_90
  case inr assump_85 =>
    cases assump_85
    case inl assump_113 =>
      have assump_177 : (((p4 ∨ True) → False) → ((p3 ∨ p0) → (p7 → p3))) := by
        intro assump_120
        intro assump_121
        intro assump_122
        cases assump_121
        case inl assump_125 =>
          exact assump_125
        case inr assump_126 =>
          have assump_178 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_135 := assump_120 assump_178
          apply False.elim assump_135
      let assump_119 := assump_1 assump_177
      apply False.elim assump_119
    case inr assump_114 =>
      have assump_179 : (((p4 ∨ True) → False) → ((p3 ∨ p0) → (p7 → p3))) := by
        intro assump_147
        intro assump_148
        intro assump_149
        cases assump_148
        case inl assump_152 =>
          exact assump_152
        case inr assump_153 =>
          have assump_180 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_162 := assump_147 assump_180
          apply False.elim assump_162
      let assump_146 := assump_1 assump_179
      apply False.elim assump_146


variable (p1 p3 p5 p2 p6 : Prop)
theorem file56_32306 : (((((False → p1) ∨ (p2 → p5)) ∧ ((p6 ∧ False) ∧ (p6 → False))) ∧ (((True ∨ p3) → False) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_13
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
      case inr assump_15 =>
        cases assump_13
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_31


variable (p4 p2 p5 p7 p0 p3 p1 : Prop)
theorem file56_33038 : (((((True → False) → (p7 → p5)) ∨ ((p2 → p3) → False)) ∨ (((p4 → False) → (p4 → p1)) → ((False → False) → False))) ∨ ((((p3 → False) → False) ∨ ((p5 ∨ p3) → False)) → (((p0 → False) ∨ (p3 → False)) ∧ ((p3 ∧ False) ∧ (True → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p6 p5 p0 p7 : Prop)
theorem file56_33528 : (((((p7 ∧ p5) ∧ (False ∨ p6)) ∨ ((True → False) → (p0 → p6))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p7 ∧ p5) ∧ (False ∨ p6)) ∨ ((True → False) → (p0 → p6))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p2 p0 p4 p3 p1 p6 : Prop)
theorem file56_34025 : (((((True → False) → False) → ((p4 ∧ False) ∧ (p4 → p3))) → False) ∧ ((((True → False) → False) ∨ ((p5 → p6) ∧ (p4 ∧ p2))) → (((p6 → False) ∧ (p0 ∨ p0)) → ((p4 → p0) ∨ (p5 ∨ p1))))) := by
  apply And.intro
  intro assump_1
  have assump_70 : ((True → False) → False) := by
    intro assump_5
    have assump_71 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_71
    apply False.elim assump_8
  let assump_4 := assump_1 assump_70
  let assump_12 := And.left assump_4
  let assump_13 := And.right assump_12
  apply False.elim assump_13
  intro assump_18
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case inl assump_24 =>
      cases assump_18
      case inl assump_28 =>
        apply Or.inl
        intro assump_32
        exact assump_24
      case inr assump_29 =>
        cases assump_29
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            apply Or.inl
            intro assump_45
            exact assump_24
    case inr assump_25 =>
      cases assump_18
      case inl assump_50 =>
        apply Or.inl
        intro assump_54
        exact assump_25
      case inr assump_51 =>
        cases assump_51
        case intro assump_57 assump_58 =>
          cases assump_58
          case intro assump_61 assump_62 =>
            apply Or.inl
            intro assump_67
            exact assump_25


variable (p4 p2 : Prop)
theorem file56_35521 : (((((True ∧ p4) ∧ (p2 → False)) → ((True → False) → False)) → False) → False) := by
  intro assump_1
  have assump_28 : (((True ∧ p4) ∧ (p2 → False)) → ((True → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_29 : True := by
          apply True.intro
        let assump_21 := assump_6 assump_29
        apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p4 p5 p3 p2 p6 p1 p0 p7 : Prop)
theorem file56_36133 : (((((p7 → False) ∧ (p7 ∨ p7)) ∧ ((p6 → p2) ∧ (p2 ∧ p6))) ∧ (((False → p4) ∧ (p3 ∨ p5)) → ((p1 ∨ p3) → (p1 ∧ p0)))) → ((((True → True) ∧ (p3 → False)) ∨ ((p6 → False) → False)) ∨ (((p5 → False) → False) ∧ ((p3 → False) → (p3 → p3))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_9
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              apply Or.inl
              apply Or.inl
              apply And.intro
              intro assump_30
              apply True.intro
              intro assump_31
              have assump_88 : p7 := by
                exact assump_14
              let assump_48 := assump_10 assump_88
              apply False.elim assump_48
        case inr assump_15 =>
          cases assump_9
          case intro assump_54 assump_55 =>
            cases assump_55
            case intro assump_58 assump_59 =>
              apply Or.inl
              apply Or.inl
              apply And.intro
              intro assump_66
              apply True.intro
              intro assump_67
              have assump_89 : p7 := by
                exact assump_15
              let assump_84 := assump_10 assump_89
              apply False.elim assump_84


variable (p7 p0 p6 p3 p5 p4 : Prop)
theorem file56_37665 : (((((p6 → False) → (p3 → p7)) ∧ ((p7 → False) → False)) ∧ (((p3 → False) ∨ (p6 → False)) → ((p3 ∨ p4) ∧ (False ∧ p6)))) → ((((p4 ∧ False) ∧ (True ∨ p7)) ∧ ((True → p4) ∨ (p5 ∧ p0))) → False)) := by
  intro assump_86
  intro assump_87
  cases assump_87
  case intro assump_88 assump_89 =>
    cases assump_88
    case intro assump_90 assump_91 =>
      cases assump_90
      case intro assump_92 assump_93 =>
        apply False.elim assump_93


variable (p4 p6 p7 p2 p5 p3 p1 : Prop)
theorem file56_38171 : (((((False → False) ∧ (False ∧ p4)) ∧ ((p5 ∧ p1) ∨ (p2 → True))) ∨ (((False ∨ True) ∧ (p6 → False)) → ((p1 ∧ p1) → False))) → ((((False ∧ p2) ∧ (p4 ∨ p2)) → ((p4 ∧ p3) ∧ (p7 → False))) ∨ (((True ∧ p6) ∨ (p6 ∧ p5)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  case inr assump_3 =>
    apply Or.inl
    intro assump_16
    apply And.intro
    apply And.intro
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
    cases assump_16
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        apply False.elim assump_25
    intro assump_29
    cases assump_16
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        apply False.elim assump_34


variable (p2 p5 p3 p6 p4 p0 : Prop)
theorem file56_39320 : (((((False ∧ p4) → False) → False) ∧ (((p2 ∧ False) ∨ (p0 → False)) → False)) → ((((p4 → False) → False) → ((p5 → False) → False)) → (((True ∨ p4) → (False → p3)) ∨ ((True → False) ∧ (p6 → p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    intro assump_12
    apply False.elim assump_12


variable (p3 p0 p4 p1 p6 p5 p7 p2 : Prop)
theorem file56_39762 : ((((((False → p1) ∨ (True → False)) → False) → (((p2 ∨ p4) ∧ (p1 ∧ False)) → False)) → ((((p0 → p0) ∨ (p3 ∨ p7)) → False) ∧ (((p6 → False) → (p1 ∧ p2)) ∨ ((p7 → False) ∧ (p4 → p5))))) → False) := by
  intro assump_1
  have assump_35 : ((((False → p1) ∨ (True → False)) → False) → (((p2 ∨ p4) ∧ (p1 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      case inr assump_10 =>
        cases assump_8
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
  let assump_4 := assump_1 assump_35
  let assump_27 := And.left assump_4
  have assump_36 : ((p0 → p0) ∨ (p3 ∨ p7)) := by
    apply Or.inl
    intro assump_29
    exact assump_29
  let assump_28 := assump_27 assump_36
  apply False.elim assump_28


variable (p5 p3 p2 p0 p1 : Prop)
theorem file56_40764 : ((((((False ∧ p5) ∧ (p0 ∧ False)) → False) ∨ (((p5 ∧ p1) ∨ (p2 ∧ False)) → ((p3 → False) ∨ (p3 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ p5) ∧ (p0 ∧ False)) → False) ∨ (((p5 ∧ p1) ∨ (p2 ∧ False)) → ((p3 → False) ∨ (p3 ∧ False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p7 : Prop)
theorem file56_41339 : ((((((p7 → False) ∧ (p0 ∨ True)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p7 → False) ∧ (p0 ∨ True)) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_40 : (False → False) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_7 assump_40
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_41 : (False → False) := by
            intro assump_30
            apply False.elim assump_30
          let assump_29 := assump_7 assump_41
          apply False.elim assump_29
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p3 p7 p5 p4 p6 p2 : Prop)
theorem file56_42284 : ((((((p4 ∨ p5) → False) ∧ ((p5 ∧ p5) ∨ (p2 ∧ p5))) → (((p4 → p2) ∨ (p5 ∨ True)) → ((p3 → p7) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_116 : ((((p4 ∨ p5) → False) ∧ ((p5 ∧ p5) ∨ (p2 ∧ p5))) → (((p4 → p2) ∨ (p5 ∨ True)) → ((p3 → p7) → (p6 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case inl assump_13 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_18
        case inl assump_21 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            have assump_117 : (p4 ∨ p5) := by
              apply Or.inr
              exact assump_24
            let assump_31 := assump_17 assump_117
            apply False.elim assump_31
        case inr assump_22 =>
          cases assump_22
          case intro assump_35 assump_36 =>
            have assump_118 : (p4 ∨ p5) := by
              apply Or.inr
              exact assump_36
            let assump_43 := assump_17 assump_118
            apply False.elim assump_43
    case inr assump_14 =>
      cases assump_14
      case inl assump_47 =>
        cases assump_5
        case intro assump_51 assump_52 =>
          cases assump_52
          case inl assump_55 =>
            cases assump_55
            case intro assump_57 assump_58 =>
              have assump_119 : (p4 ∨ p5) := by
                apply Or.inr
                exact assump_58
              let assump_65 := assump_51 assump_119
              apply False.elim assump_65
          case inr assump_56 =>
            cases assump_56
            case intro assump_69 assump_70 =>
              have assump_120 : (p4 ∨ p5) := by
                apply Or.inr
                exact assump_70
              let assump_77 := assump_51 assump_120
              apply False.elim assump_77
      case inr assump_48 =>
        cases assump_5
        case intro assump_83 assump_84 =>
          cases assump_84
          case inl assump_87 =>
            cases assump_87
            case intro assump_89 assump_90 =>
              have assump_121 : (p4 ∨ p5) := by
                apply Or.inr
                exact assump_90
              let assump_97 := assump_83 assump_121
              apply False.elim assump_97
          case inr assump_88 =>
            cases assump_88
            case intro assump_101 assump_102 =>
              have assump_122 : (p4 ∨ p5) := by
                apply Or.inr
                exact assump_102
              let assump_109 := assump_83 assump_122
              apply False.elim assump_109
  let assump_4 := assump_1 assump_116
  apply False.elim assump_4


variable (p6 p1 p2 p5 p3 p0 : Prop)
theorem file56_45010 : (((((p0 → False) → (p2 ∨ p0)) ∧ ((p1 → False) ∧ (p6 ∧ p1))) → False) ∨ ((((p5 ∨ p2) → False) → False) ∧ (((p1 → p1) ∨ (True → p3)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_22 : p1 := by
          exact assump_11
        let assump_18 := assump_6 assump_22
        apply False.elim assump_18


variable (p1 p5 p6 p2 p7 : Prop)
theorem file56_45553 : ((((((p7 ∨ True) ∨ (p7 → False)) ∨ ((p5 → p2) → (p6 → p1))) ∨ (((p1 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p7 ∨ True) ∨ (p7 → False)) ∨ ((p5 → p2) → (p6 → p1))) ∨ (((p1 → False) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p3 p2 p6 p5 p7 p1 p0 : Prop)
theorem file56_46027 : ((((((p4 ∨ p7) ∧ (p2 ∨ p2)) ∧ ((p2 → False) ∧ (True ∧ p0))) → False) ∧ ((((p3 ∧ False) ∨ (p6 → p6)) → False) ∧ (((False ∨ False) ∧ (p0 ∨ p1)) ∨ ((p5 → False) ∧ (p2 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_20 assump_21 =>
          have assump_35 : ((p3 ∧ False) ∨ (p6 → p6)) := by
            apply Or.inr
            intro assump_29
            exact assump_29
          let assump_28 := assump_6 assump_35
          apply False.elim assump_28


variable (p4 p6 p2 p7 : Prop)
theorem file56_46997 : (((((p7 → p4) ∨ (p6 → False)) ∨ ((p6 ∨ p4) → False)) → (((True ∨ False) → (True ∨ p2)) ∨ ((p7 ∨ True) → (p7 → False)))) ∨ ((((p2 → False) → (False ∧ p6)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      cases assump_8
      case inl assump_9 =>
        apply Or.inl
        apply True.intro
      case inr assump_10 =>
        apply False.elim assump_10
    case inr assump_5 =>
      apply Or.inl
      intro assump_17
      cases assump_17
      case inl assump_18 =>
        apply Or.inl
        apply True.intro
      case inr assump_19 =>
        apply False.elim assump_19
  case inr assump_3 =>
    apply Or.inl
    intro assump_26
    cases assump_26
    case inl assump_27 =>
      apply Or.inl
      apply True.intro
    case inr assump_28 =>
      apply False.elim assump_28


variable (p2 p4 p7 p5 p0 p1 : Prop)
theorem file56_47981 : ((((((p0 ∨ True) ∨ (p0 ∧ p7)) ∨ ((p0 → p2) ∨ (p7 ∧ p1))) → (((True → False) → (p5 → p2)) ∨ ((p4 → False) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_85 : ((((p0 ∨ True) ∨ (p0 ∧ p7)) ∨ ((p0 → p2) ∨ (p7 ∧ p1))) → (((True → False) → (p5 → p2)) ∨ ((p4 → False) ∨ (True → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          intro assump_14
          intro assump_15
          have assump_86 : True := by
            apply True.intro
          let assump_20 := assump_14 assump_86
          apply False.elim assump_20
        case inr assump_11 =>
          apply Or.inl
          intro assump_26
          intro assump_27
          have assump_87 : True := by
            apply True.intro
          let assump_32 := assump_26 assump_87
          apply False.elim assump_32
      case inr assump_9 =>
        cases assump_9
        case intro assump_36 assump_37 =>
          apply Or.inl
          intro assump_42
          intro assump_43
          have assump_88 : True := by
            apply True.intro
          let assump_48 := assump_42 assump_88
          apply False.elim assump_48
    case inr assump_7 =>
      cases assump_7
      case inl assump_52 =>
        apply Or.inl
        intro assump_56
        intro assump_57
        have assump_89 : True := by
          apply True.intro
        let assump_62 := assump_56 assump_89
        apply False.elim assump_62
      case inr assump_53 =>
        cases assump_53
        case intro assump_66 assump_67 =>
          apply Or.inl
          intro assump_72
          intro assump_73
          have assump_90 : True := by
            apply True.intro
          let assump_78 := assump_72 assump_90
          apply False.elim assump_78
  let assump_4 := assump_1 assump_85
  apply False.elim assump_4


variable (p3 p5 p7 p4 p1 p6 : Prop)
theorem file56_49990 : ((((((False → p6) ∨ (p1 ∧ p3)) → ((p4 → False) → (p4 ∧ p5))) → False) ∧ ((((p4 → False) → (p1 ∧ p1)) → ((False → True) ∨ (p1 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p4 → False) → (p1 ∧ p1)) → ((False → True) ∨ (p1 → p7))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      apply True.intro
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p2 p4 p7 p6 p1 p3 p0 : Prop)
theorem file56_50520 : (((((True ∨ p4) → False) ∧ ((p1 → False) ∨ (p4 → p4))) → False) ∨ ((((p0 ∧ False) → False) → ((p2 → p0) ∧ (True → False))) ∨ (((p6 → False) ∧ (p3 ∨ p1)) → ((p6 → False) ∨ (p7 → True))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_22 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_11 := assump_2 assump_22
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_23 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_18 := assump_2 assump_23
      apply False.elim assump_18


variable (p0 p4 p1 p5 p3 p2 p6 : Prop)
theorem file56_51252 : (((((p3 ∧ p1) → False) → ((False ∨ p3) → (p3 → False))) ∧ (((p6 → p0) ∧ (p0 ∧ p1)) ∨ ((False → p4) ∧ (p2 ∧ p6)))) → ((((False → False) → False) → ((p1 ∧ True) → (p5 → p2))) ∨ (((p6 → p3) → (p6 ∨ False)) → ((p5 ∧ p6) ∧ (False ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          intro assump_19
          intro assump_20
          cases assump_19
          case intro assump_23 assump_24 =>
            have assump_61 : (False → False) := by
              intro assump_32
              apply False.elim assump_32
            let assump_31 := assump_18 assump_61
            apply False.elim assump_31
    case inr assump_7 =>
      cases assump_7
      case intro assump_38 assump_39 =>
        cases assump_39
        case intro assump_42 assump_43 =>
          apply Or.inl
          intro assump_48
          intro assump_49
          intro assump_50
          cases assump_49
          case intro assump_53 assump_54 =>
            exact assump_42


variable (p0 p6 p4 p3 p1 p5 p7 p2 : Prop)
theorem file56_52527 : (((((p5 ∧ False) ∧ (p2 → False)) ∧ ((p1 ∨ True) ∨ (p6 → p0))) → (((False ∨ p1) ∧ (p3 ∧ p4)) → False)) ∨ ((((p6 → False) ∧ (p3 ∨ p1)) ∨ ((p7 → p1) → False)) ∧ (((p1 ∨ p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              apply False.elim assump_22


variable (p6 p5 p7 p1 p0 p3 : Prop)
theorem file56_53295 : (((((False → p0) → False) ∧ ((p1 ∧ p6) → False)) ∧ (((False ∨ p0) ∧ (False ∨ p7)) ∨ ((p1 ∨ p1) ∧ (p5 → p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            cases assump_13
            case inl assump_20 =>
              apply False.elim assump_20
            case inr assump_21 =>
              have assump_68 : (False → p0) := by
                intro assump_30
                apply False.elim assump_30
              let assump_29 := assump_4 assump_68
              apply False.elim assump_29
      case inr assump_11 =>
        cases assump_11
        case intro assump_36 assump_37 =>
          cases assump_36
          case inl assump_38 =>
            have assump_69 : (False → p0) := by
              intro assump_48
              apply False.elim assump_48
            let assump_47 := assump_4 assump_69
            apply False.elim assump_47
          case inr assump_39 =>
            have assump_70 : (False → p0) := by
              intro assump_62
              apply False.elim assump_62
            let assump_61 := assump_4 assump_70
            apply False.elim assump_61


variable (p7 p0 p1 p5 p4 : Prop)
theorem file56_54793 : ((((((p5 ∧ p7) → False) ∧ ((p7 ∨ p7) ∧ (p1 → p0))) → False) ∧ ((((False ∧ p4) → False) ∨ ((False → True) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((False ∧ p4) → False) ∨ ((False → True) → False)) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p2 p0 p7 p4 : Prop)
theorem file56_55339 : (((((p2 → True) ∨ (True → p7)) ∨ ((p4 ∧ False) ∨ (p0 ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p2 → True) ∨ (True → p7)) ∨ ((p4 ∧ False) ∨ (p0 ∨ p2))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p7 p0 p2 p3 p5 : Prop)
theorem file56_55719 : ((((((p3 ∨ p0) → False) → ((p5 → False) → False)) → (((p2 ∧ p3) → (True ∨ p3)) ∨ ((p7 ∧ False) ∧ (p2 ∨ p2)))) → False) → False) := by
  intro assump_16
  have assump_33 : ((((p3 ∨ p0) → False) → ((p5 → False) → False)) → (((p2 ∧ p3) → (True ∨ p3)) ∨ ((p7 ∧ False) ∧ (p2 ∨ p2)))) := by
    intro assump_20
    apply Or.inl
    intro assump_23
    cases assump_23
    case intro assump_24 assump_25 =>
      apply Or.inl
      apply True.intro
  let assump_19 := assump_16 assump_33
  apply False.elim assump_19


variable (p0 p5 p6 p3 : Prop)
theorem file56_56283 : ((((((p6 ∧ p6) ∧ (p6 ∨ p5)) → ((False → True) → (True ∧ p6))) ∨ (((True → p0) → False) ∧ ((False ∨ p3) ∧ (p6 → False)))) → False) → False) := by
  intro assump_5
  have assump_30 : ((((p6 ∧ p6) ∧ (p6 ∨ p5)) → ((False → True) → (True ∧ p6))) ∨ (((True → p0) → False) ∧ ((False ∨ p3) ∧ (p6 → False)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    apply And.intro
    apply True.intro
    cases assump_9
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_14
        case inl assump_21 =>
          exact assump_21
        case inr assump_22 =>
          exact assump_16
  let assump_8 := assump_5 assump_30
  apply False.elim assump_8


variable (p1 p2 p7 p4 : Prop)
theorem file56_57060 : (((((p4 ∧ False) ∨ (p2 → False)) → ((p1 → p7) ∧ (p4 → p2))) ∧ (((True ∨ p7) ∨ (p7 ∨ False)) → ((p4 → p1) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((True ∨ p7) ∨ (p7 ∨ False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    let assump_9 := And.right assump_8
    have assump_16 : True := by
      apply True.intro
    let assump_11 := assump_9 assump_16
    apply False.elim assump_11


variable (p6 p2 p3 p5 p7 p1 : Prop)
theorem file56_57649 : ((((((p3 ∧ p7) ∧ (p2 → False)) ∨ ((p6 ∧ p1) ∧ (True → False))) ∨ (((p5 → True) ∨ (p3 ∨ p7)) ∨ ((p1 → p2) → (p2 → False)))) → ((((p2 → False) → (p1 → True)) → ((False → False) ∨ (True → p6))) → False)) → False) := by
  intro assump_1
  have assump_16 : ((((p3 ∧ p7) ∧ (p2 → False)) ∨ ((p6 ∧ p1) ∧ (True → False))) ∨ (((p5 → True) ∨ (p3 ∨ p7)) ∨ ((p1 → p2) → (p2 → False)))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_16
  have assump_17 : (((p2 → False) → (p1 → True)) → ((False → False) ∨ (True → p6))) := by
    intro assump_7
    apply Or.inl
    intro assump_10
    apply False.elim assump_10
  let assump_6 := assump_4 assump_17
  apply False.elim assump_6


variable (p5 p4 p2 p0 p7 p3 p1 p6 : Prop)
theorem file56_58464 : (((((p2 ∧ True) → (p3 ∧ p7)) → False) → (((True → False) → (p6 → False)) → ((False → False) → (p4 ∨ True)))) ∨ ((((p1 ∧ p1) → (True ∨ p4)) ∨ ((True ∨ p4) ∨ (p2 ∧ p7))) ∨ (((p5 → False) ∨ (p2 ∧ False)) → ((p0 ∧ p2) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inr
  apply True.intro


variable (p6 p4 p1 p3 p7 p2 p5 : Prop)
theorem file56_58859 : ((((((False → p4) ∨ (p1 ∧ False)) ∨ ((p6 → p6) ∨ (p5 → False))) ∧ (((p2 → True) → False) → ((p2 → p6) ∧ (p7 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((False → p4) ∨ (p1 ∧ False)) ∨ ((p6 → p6) ∨ (p5 → False))) ∧ (((p2 → True) → False) → ((p2 → p6) ∧ (p7 ∨ p3)))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    apply And.intro
    intro assump_9
    have assump_30 : (p2 → True) := by
      intro assump_15
      apply True.intro
    let assump_14 := assump_8 assump_30
    apply False.elim assump_14
    have assump_31 : (p2 → True) := by
      intro assump_22
      apply True.intro
    let assump_21 := assump_8 assump_31
    apply False.elim assump_21
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p0 : Prop)
theorem file56_59741 : (((((False → p2) → (p0 ∧ False)) → False) → False) → False) := by
  intro assump_10
  have assump_29 : (((False → p2) → (p0 ∧ False)) → False) := by
    intro assump_14
    have assump_30 : (False → p2) := by
      intro assump_18
      apply False.elim assump_18
    let assump_17 := assump_14 assump_30
    let assump_21 := And.right assump_17
    apply False.elim assump_21
  let assump_13 := assump_10 assump_29
  apply False.elim assump_13


variable (p4 p1 p0 p7 p5 : Prop)
theorem file56_60243 : ((((((p0 ∨ p1) → (False → True)) ∨ ((p5 → True) ∧ (p1 ∨ p1))) ∨ (((p4 ∨ True) ∧ (p7 → True)) → ((p4 → False) ∧ (p4 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_10 : ((((p0 ∨ p1) → (False → True)) ∨ ((p5 → True) ∧ (p1 ∨ p1))) ∨ (((p4 ∨ True) ∧ (p7 → True)) → ((p4 → False) ∧ (p4 ∨ False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p6 p7 : Prop)
theorem file56_60767 : (((((False ∧ p7) ∨ (p6 ∧ False)) → False) → False) → False) := by
  intro assump_1
  have assump_21 : (((False ∧ p7) ∨ (p6 ∧ False)) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_7 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p2 p0 p7 p4 p5 p6 p1 p3 : Prop)
theorem file56_61323 : (((((p3 → False) → (p5 → False)) → False) → (((p1 → False) ∨ (p5 ∧ p7)) → ((p6 ∧ p0) ∨ (p2 → False)))) → ((((p5 → False) → (p5 → False)) ∨ ((p3 ∧ p6) → (p7 ∨ p3))) ∨ (((p4 → False) → (False → p3)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_14 : p5 := by
    exact assump_5
  let assump_10 := assump_4 assump_14
  apply False.elim assump_10


variable (p3 p2 p5 p6 p0 p7 : Prop)
theorem file56_61792 : (((((p7 → p2) → False) ∨ ((p0 → p3) → False)) → (((False ∨ p6) → (p3 → p3)) → ((True ∨ p6) ∨ (p3 ∧ p5)))) ∨ ((((p2 → True) ∧ (p2 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_6 =>
    apply Or.inl
    apply Or.inl
    apply True.intro


variable (p3 p6 p1 p5 p4 p2 p7 p0 : Prop)
theorem file56_62244 : (((((p2 ∨ p3) ∨ (True → False)) → ((True ∧ True) → False)) ∧ (((p1 → False) ∧ (p5 ∧ p0)) ∧ ((True ∨ p4) ∧ (p3 → p0)))) → ((((p5 → False) ∧ (p7 ∨ p4)) → False) ∨ (((p3 → p0) → (p6 → p6)) ∨ ((p6 ∧ p4) ∨ (True ∨ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              apply Or.inl
              intro assump_26
              cases assump_26
              case intro assump_27 assump_28 =>
                cases assump_28
                case inl assump_31 =>
                  have assump_72 : p5 := by
                    exact assump_12
                  let assump_36 := assump_27 assump_72
                  apply False.elim assump_36
                case inr assump_32 =>
                  have assump_73 : p5 := by
                    exact assump_12
                  let assump_43 := assump_27 assump_73
                  apply False.elim assump_43
            case inr assump_21 =>
              apply Or.inl
              intro assump_51
              cases assump_51
              case intro assump_52 assump_53 =>
                cases assump_53
                case inl assump_56 =>
                  have assump_74 : p5 := by
                    exact assump_12
                  let assump_61 := assump_52 assump_74
                  apply False.elim assump_61
                case inr assump_57 =>
                  have assump_75 : p5 := by
                    exact assump_12
                  let assump_68 := assump_52 assump_75
                  apply False.elim assump_68


variable (p4 p0 p1 p5 p3 p6 : Prop)
theorem file56_64145 : (((((True → False) → False) → ((p6 ∨ False) ∨ (p0 → False))) ∧ (((p1 → p5) → (p3 ∧ p4)) ∧ ((p5 → False) ∧ (True → False)))) → ((((False → False) → (p5 ∨ p5)) ∨ ((p0 ∨ p1) → (p6 ∨ True))) ∧ (((p5 ∨ p0) → False) → False))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        have assump_45 : True := by
          apply True.intro
        let assump_20 := assump_11 assump_45
        apply False.elim assump_20
  intro assump_24
  cases assump_1
  case intro assump_27 assump_28 =>
    cases assump_28
    case intro assump_31 assump_32 =>
      cases assump_32
      case intro assump_35 assump_36 =>
        have assump_46 : True := by
          apply True.intro
        let assump_41 := assump_36 assump_46
        apply False.elim assump_41


variable (p6 p7 p5 : Prop)
theorem file56_65147 : ((((((True → False) ∨ (p6 → p5)) ∧ ((p7 ∨ True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((True → False) ∨ (p6 → p5)) ∧ ((p7 ∨ True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_30 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_14 := assump_7 assump_30
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_31 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_22 := assump_7 assump_31
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p3 p2 p5 p1 : Prop)
theorem file56_65960 : ((((((True ∧ p3) ∧ (p7 ∧ False)) → ((p2 ∨ True) ∨ (True ∨ p7))) ∨ (((True → p1) → (p3 → False)) ∨ ((p5 ∨ p1) → (p2 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((True ∧ p3) ∧ (p7 ∧ False)) → ((p2 ∨ True) ∨ (True ∨ p7))) ∨ (((True → p1) → (p3 → False)) ∨ ((p5 ∨ p1) → (p2 ∧ True)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p7 p3 p5 p6 p4 p0 : Prop)
theorem file56_66653 : (((((p4 → True) ∨ (p6 ∧ p3)) → False) → False) ∨ ((((p5 ∧ p6) ∨ (False ∧ p6)) ∧ ((p0 ∨ p4) → False)) ∧ (((True ∨ p5) → (p7 → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p4 → True) ∨ (p6 ∧ p3)) := by
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p0 p1 p6 p2 p7 p3 p5 p4 : Prop)
theorem file56_67069 : (((((p0 → False) → (p7 ∧ p7)) ∨ ((p3 → False) ∧ (True ∨ p4))) ∨ (((p0 → p1) → (p0 ∨ p6)) → False)) → ((((p4 → p7) → (p0 → p1)) ∨ ((False → p4) → False)) → (((False ∧ p0) ∨ (p2 ∨ False)) → ((p3 ∨ p2) ∨ (p5 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  case inr assump_5 =>
    cases assump_5
    case inl assump_10 =>
      cases assump_2
      case inl assump_14 =>
        cases assump_1
        case inl assump_18 =>
          cases assump_18
          case inl assump_20 =>
            apply Or.inl
            apply Or.inr
            exact assump_10
          case inr assump_21 =>
            cases assump_21
            case intro assump_24 assump_25 =>
              cases assump_25
              case inl assump_28 =>
                apply Or.inl
                apply Or.inr
                exact assump_10
              case inr assump_29 =>
                apply Or.inl
                apply Or.inr
                exact assump_10
        case inr assump_19 =>
          apply Or.inl
          apply Or.inr
          exact assump_10
      case inr assump_15 =>
        cases assump_1
        case inl assump_38 =>
          cases assump_38
          case inl assump_40 =>
            apply Or.inl
            apply Or.inr
            exact assump_10
          case inr assump_41 =>
            cases assump_41
            case intro assump_44 assump_45 =>
              cases assump_45
              case inl assump_48 =>
                apply Or.inl
                apply Or.inr
                exact assump_10
              case inr assump_49 =>
                apply Or.inl
                apply Or.inr
                exact assump_10
        case inr assump_39 =>
          apply Or.inl
          apply Or.inr
          exact assump_10
    case inr assump_11 =>
      apply False.elim assump_11


variable (p7 p2 p5 : Prop)
theorem file56_69084 : (((((p2 ∨ p7) ∨ (False ∨ True)) → False) → False) ∨ ((((p7 → False) ∧ (p5 → False)) → False) → (((p7 ∨ p5) ∨ (p7 ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p2 ∨ p7) ∨ (False ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p2 p1 p0 p4 p7 p5 : Prop)
theorem file56_69488 : ((((((True → p0) ∧ (True ∨ p5)) ∧ ((p4 ∧ p4) ∧ (p0 ∧ False))) ∧ (((p7 → p0) → False) ∧ ((p2 ∨ p0) ∨ (p7 → p3)))) ∧ ((((p1 → False) → False) → False) → (((p0 → p7) → (p3 → p5)) → False))) → False) := by
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
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
          case inr assump_13 =>
            cases assump_7
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_33
                case intro assump_40 assump_41 =>
                  apply False.elim assump_41


variable (p3 p4 p2 : Prop)
theorem file56_70631 : ((((((False ∨ p3) ∨ (True ∧ True)) → False) → (((False → False) → (p4 ∨ p2)) ∨ ((False → False) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False ∨ p3) ∨ (True ∧ True)) → False) → (((False → False) → (p4 ∨ p2)) ∨ ((False → False) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_20 : ((False ∨ p3) ∨ (True ∧ True)) := by
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p2 p1 p0 p4 : Prop)
theorem file56_71302 : ((((((p1 → False) ∨ (p4 → False)) → ((True ∨ p0) ∨ (p2 ∧ False))) → False) ∧ ((((p6 ∨ True) ∨ (p1 → False)) ∨ ((True ∨ False) ∧ (p0 → True))) → False)) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    have assump_29 : (((p6 ∨ True) ∨ (p1 → False)) ∨ ((True ∨ False) ∧ (p0 → True))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_25 := assump_20 assump_29
    apply False.elim assump_25


variable (p2 p7 p5 p1 p3 p0 p4 : Prop)
theorem file56_71847 : (((((p4 ∧ p7) → False) ∧ ((p7 ∨ p4) ∧ (p5 ∧ p2))) → (((True ∧ p3) ∧ (p2 ∨ p0)) ∧ ((p0 ∨ p5) ∨ (p2 → p2)))) → ((((p5 ∨ p1) → False) ∧ ((p4 ∨ p5) ∧ (p4 ∧ False))) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_12
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      case inr assump_14 =>
        cases assump_12
        case intro assump_25 assump_26 =>
          apply False.elim assump_26


variable (p1 p2 p0 p5 p4 : Prop)
theorem file56_72507 : ((((((p5 ∨ True) ∨ (False → False)) ∨ ((p2 → p4) → False)) ∨ (((p0 → False) → (False ∧ p1)) ∨ ((p5 → False) → False))) → False) → False) := by
  intro assump_26
  have assump_33 : ((((p5 ∨ True) ∨ (False → False)) ∨ ((p2 → p4) → False)) ∨ (((p0 → False) → (False ∧ p1)) ∨ ((p5 → False) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_29 := assump_26 assump_33
  apply False.elim assump_29


variable (p7 p0 p5 p2 p1 p4 : Prop)
theorem file56_73027 : (((((p5 → False) → (p4 → False)) ∨ ((p2 → p1) ∨ (False → p0))) → False) → ((((p1 → p0) ∧ (True → False)) → False) → (((p4 ∨ p0) ∧ (True ∨ p4)) ∨ ((False → False) ∨ (p7 ∧ True))))) := by
  intro assump_12
  intro assump_13
  apply Or.inr
  apply Or.inl
  intro assump_18
  apply False.elim assump_18


variable (p3 p6 p4 : Prop)
theorem file56_73377 : (((((False → p6) ∨ (p6 ∧ p3)) ∧ ((p4 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p6) ∨ (p6 ∧ p3)) ∧ ((p4 ∧ False) → False)) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p0 p6 p1 p5 p7 : Prop)
theorem file56_73872 : (((((True ∨ p3) → False) → ((True → p7) ∨ (p6 → False))) → False) → ((((p3 → False) ∧ (p0 ∨ p5)) → False) ∧ (((p1 ∨ p6) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      have assump_64 : (((True ∨ p3) → False) → ((True → p7) ∨ (p6 → False))) := by
        intro assump_14
        apply Or.inl
        intro assump_17
        have assump_65 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_20 := assump_14 assump_65
        apply False.elim assump_20
      let assump_13 := assump_1 assump_64
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_66 : (((True ∨ p3) → False) → ((True → p7) ∨ (p6 → False))) := by
        intro assump_32
        apply Or.inl
        intro assump_35
        have assump_67 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_38 := assump_32 assump_67
        apply False.elim assump_38
      let assump_31 := assump_1 assump_66
      apply False.elim assump_31
  intro assump_45
  have assump_68 : (((True ∨ p3) → False) → ((True → p7) ∨ (p6 → False))) := by
    intro assump_51
    apply Or.inl
    intro assump_54
    have assump_69 : (True ∨ p3) := by
      apply Or.inl
      apply True.intro
    let assump_57 := assump_51 assump_69
    apply False.elim assump_57
  let assump_50 := assump_1 assump_68
  apply False.elim assump_50


variable (p3 p5 p1 : Prop)
theorem file56_75418 : ((((((False → False) ∨ (True ∨ p5)) → False) → (((True → False) ∧ (p1 ∧ False)) → ((True → False) ∨ (p3 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False → False) ∨ (True ∨ p5)) → False) → (((True → False) ∧ (p1 ∧ False)) → ((True → False) ∨ (p3 ∨ False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p0 p6 p7 p4 p3 : Prop)
theorem file56_76028 : (((((p1 ∧ True) ∨ (False ∨ p3)) ∨ ((p7 ∨ True) ∨ (False ∨ p0))) → False) → ((((p4 ∧ True) ∧ (False ∨ p1)) ∨ ((p6 → p6) → False)) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case inl assump_7 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case inl assump_17 =>
          apply False.elim assump_17
        case inr assump_18 =>
          have assump_37 : (((p1 ∧ True) ∨ (False ∨ p3)) ∨ ((p7 ∨ True) ∨ (False ∨ p0))) := by
            apply Or.inl
            apply Or.inl
            apply And.intro
            exact assump_18
            apply True.intro
          let assump_25 := assump_5 assump_37
          apply False.elim assump_25
  case inr assump_8 =>
    have assump_38 : (((p1 ∧ True) ∨ (False ∨ p3)) ∨ ((p7 ∨ True) ∨ (False ∨ p0))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_33 := assump_5 assump_38
    apply False.elim assump_33


variable (p7 p5 p2 p3 : Prop)
theorem file56_77115 : (((((p5 ∨ p3) ∧ (p5 → p7)) ∧ ((p7 ∧ False) ∧ (p2 ∨ p3))) ∧ (((False → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
        case inr assump_9 =>
          cases assump_5
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply False.elim assump_29


variable (p4 p1 p6 p0 p5 : Prop)
theorem file56_77914 : (((((p5 → p4) → (p6 → False)) → False) ∧ (((p4 ∧ False) ∨ (p6 → p6)) → False)) → ((((True → False) ∨ (p6 ∧ p6)) ∨ ((p0 → p1) → (True → False))) ∨ (((p5 → p0) → False) ∧ ((p0 ∧ p5) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_18 : ((p4 ∧ False) ∨ (p6 → p6)) := by
      apply Or.inr
      intro assump_12
      exact assump_12
    let assump_11 := assump_3 assump_18
    apply False.elim assump_11


variable (p2 p7 p0 p6 p3 p4 p5 : Prop)
theorem file56_78501 : (((((p2 ∨ p5) ∧ (p2 ∧ p5)) → ((p6 ∨ p3) ∨ (True ∨ p0))) ∨ (((p2 ∨ p4) → False) ∧ ((p7 → False) → False))) ∨ ((((p5 ∧ True) ∧ (p4 ∨ p4)) → ((False → False) ∧ (p5 ∨ p2))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inr
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      cases assump_3
      case intro assump_16 assump_17 =>
        apply Or.inr
        apply Or.inl
        apply True.intro


variable (p5 p4 p1 p2 p6 p0 p3 : Prop)
theorem file56_79170 : ((((((p0 → False) → (p3 ∨ p2)) ∨ ((p6 ∨ p5) ∧ (True ∧ p1))) → (((p5 ∨ p4) → False) ∧ ((p5 → p0) → (False ∨ p3)))) ∧ ((((p2 ∧ p3) ∧ (False ∧ p4)) → ((p3 → p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((p2 ∧ p3) ∧ (False ∧ p4)) → ((p3 → p0) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
    let assump_8 := assump_3 assump_28
    apply False.elim assump_8


variable (p2 p7 p0 : Prop)
theorem file56_79908 : (((((p7 → True) ∨ (p2 ∧ p2)) ∨ ((p0 → True) → False)) → False) → False) := by
  intro assump_22
  have assump_30 : (((p7 → True) ∨ (p2 ∧ p2)) ∨ ((p0 → True) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_26
    apply True.intro
  let assump_25 := assump_22 assump_30
  apply False.elim assump_25


variable (p0 p4 p2 p1 p7 p3 p5 p6 : Prop)
theorem file56_80290 : (((((False ∧ p2) → False) → False) ∧ (((p3 → p3) → (p4 → False)) ∧ ((p2 ∨ True) ∨ (False → False)))) → ((((p6 ∧ p2) → False) ∧ ((p3 ∨ False) ∧ (p4 → False))) ∨ (((p5 ∨ p7) → (p4 ∨ p0)) ∨ ((True ∧ p1) → False)))) := by
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_31
    case intro assump_34 assump_35 =>
      cases assump_35
      case inl assump_38 =>
        cases assump_38
        case inl assump_40 =>
          apply Or.inr
          apply Or.inl
          intro assump_68
          cases assump_68
          case inl assump_69 =>
            have assump_234 : ((False ∧ p2) → False) := by
              intro assump_81
              cases assump_81
              case intro assump_82 assump_83 =>
                apply False.elim assump_82
            let assump_80 := assump_30 assump_234
            apply False.elim assump_80
          case inr assump_70 =>
            have assump_235 : ((False ∧ p2) → False) := by
              intro assump_99
              cases assump_99
              case intro assump_100 assump_101 =>
                apply False.elim assump_100
            let assump_98 := assump_30 assump_235
            apply False.elim assump_98
        case inr assump_41 =>
          apply Or.inr
          apply Or.inl
          intro assump_132
          cases assump_132
          case inl assump_133 =>
            have assump_236 : ((False ∧ p2) → False) := by
              intro assump_144
              cases assump_144
              case intro assump_145 assump_146 =>
                apply False.elim assump_145
            let assump_143 := assump_30 assump_236
            apply False.elim assump_143
          case inr assump_134 =>
            have assump_237 : ((False ∧ p2) → False) := by
              intro assump_161
              cases assump_161
              case intro assump_162 assump_163 =>
                apply False.elim assump_162
            let assump_160 := assump_30 assump_237
            apply False.elim assump_160
      case inr assump_39 =>
        apply Or.inr
        apply Or.inl
        intro assump_195
        cases assump_195
        case inl assump_196 =>
          have assump_238 : ((False ∧ p2) → False) := by
            intro assump_208
            cases assump_208
            case intro assump_209 assump_210 =>
              apply False.elim assump_209
          let assump_207 := assump_30 assump_238
          apply False.elim assump_207
        case inr assump_197 =>
          have assump_239 : ((False ∧ p2) → False) := by
            intro assump_226
            cases assump_226
            case intro assump_227 assump_228 =>
              apply False.elim assump_227
          let assump_225 := assump_30 assump_239
          apply False.elim assump_225


variable (p0 p5 p2 p4 p6 p7 : Prop)
theorem file56_83139 : ((((((p7 ∧ p6) ∨ (p5 ∧ False)) ∧ ((p6 → False) → (False ∧ p4))) → (((p2 ∧ p6) → (True → False)) → ((p7 ∨ p4) → (p7 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_57 : ((((p7 ∧ p6) ∨ (p5 ∧ False)) ∧ ((p6 → False) → (False ∧ p4))) → (((p2 ∧ p6) → (True → False)) → ((p7 ∨ p4) → (p7 ∨ p0)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply Or.inl
            exact assump_18
        case inr assump_17 =>
          cases assump_17
          case intro assump_26 assump_27 =>
            apply False.elim assump_27
    case inr assump_9 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        cases assump_36
        case inl assump_38 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply Or.inl
            exact assump_40
        case inr assump_39 =>
          cases assump_39
          case intro assump_48 assump_49 =>
            apply False.elim assump_49
  let assump_4 := assump_1 assump_57
  apply False.elim assump_4


variable (p7 p3 p1 p4 p2 p5 p6 : Prop)
theorem file56_84459 : (((((p5 ∧ p2) → False) → False) → (((p1 → False) → False) → ((p2 ∧ p4) → (True → True)))) ∨ ((((p5 → p7) ∧ (p5 ∧ p1)) → ((True ∨ p2) → (p1 ∧ p3))) → (((p3 → False) ∧ (p2 → p5)) ∧ ((p5 ∨ p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply True.intro


variable (p6 p5 p4 p0 p7 : Prop)
theorem file56_84826 : (((((p6 ∧ False) → (p6 ∨ p5)) ∨ ((p7 → False) ∨ (p5 → False))) → (((p4 ∧ p4) → False) ∧ ((True → False) ∧ (p0 ∧ False)))) → False) := by
  intro assump_1
  have assump_19 : (((p6 ∧ False) → (p6 ∨ p5)) ∨ ((p7 → False) ∨ (p5 → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_19
  let assump_12 := And.right assump_4
  let assump_14 := And.left assump_12
  have assump_20 : True := by
    apply True.intro
  let assump_15 := assump_14 assump_20
  apply False.elim assump_15


variable (p4 p0 p2 p5 p3 p6 : Prop)
theorem file56_85481 : ((((((p0 ∧ p4) → False) ∨ ((p5 ∧ p5) ∨ (p2 → p5))) ∨ (((p6 → False) → False) → False)) ∧ ((((True → p6) → (p3 → p6)) ∨ ((True → True) → (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_78 : (((True → p6) → (p3 → p6)) ∨ ((True → True) → (p0 → False))) := by
          apply Or.inl
          intro assump_13
          intro assump_14
          have assump_79 : True := by
            apply True.intro
          let assump_19 := assump_13 assump_79
          exact assump_19
        let assump_12 := assump_3 assump_78
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case inl assump_24 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            have assump_80 : (((True → p6) → (p3 → p6)) ∨ ((True → True) → (p0 → False))) := by
              apply Or.inl
              intro assump_35
              intro assump_36
              have assump_81 : True := by
                apply True.intro
              let assump_41 := assump_35 assump_81
              exact assump_41
            let assump_34 := assump_3 assump_80
            apply False.elim assump_34
        case inr assump_25 =>
          have assump_82 : (((True → p6) → (p3 → p6)) ∨ ((True → True) → (p0 → False))) := by
            apply Or.inl
            intro assump_51
            intro assump_52
            have assump_83 : True := by
              apply True.intro
            let assump_57 := assump_51 assump_83
            exact assump_57
          let assump_50 := assump_3 assump_82
          apply False.elim assump_50
    case inr assump_5 =>
      have assump_84 : (((True → p6) → (p3 → p6)) ∨ ((True → True) → (p0 → False))) := by
        apply Or.inl
        intro assump_67
        intro assump_68
        have assump_85 : True := by
          apply True.intro
        let assump_73 := assump_67 assump_85
        exact assump_73
      let assump_66 := assump_3 assump_84
      apply False.elim assump_66


variable (p3 p2 p7 p0 p4 p5 : Prop)
theorem file56_87666 : (((((p7 ∨ p5) ∨ (p0 ∧ p4)) → ((p2 ∧ p5) ∧ (False ∨ False))) → False) → ((((True ∨ True) ∧ (p2 ∧ p2)) ∧ ((p2 ∨ p2) ∧ (p3 → False))) ∨ (((p7 → p7) ∨ (p5 → p3)) → ((p3 ∨ p7) → (p3 → p3))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    cases assump_4
    case inl assump_13 =>
      exact assump_9
    case inr assump_14 =>
      exact assump_9
  case inr assump_10 =>
    cases assump_4
    case inl assump_21 =>
      exact assump_6
    case inr assump_22 =>
      exact assump_6


variable (p3 p6 p4 p0 p2 p7 : Prop)
theorem file56_88292 : (((((p6 ∧ p4) ∧ (False → False)) ∨ ((p7 ∧ p4) → (p2 ∨ True))) ∨ (((False ∨ p4) → (p6 ∧ p0)) ∧ ((p3 → False) → False))) ∨ ((((True → False) → (p0 ∨ False)) → ((p3 ∨ True) → False)) ∨ (((p4 → False) ∨ (False ∧ p2)) → ((False ∧ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    apply True.intro


variable (p2 p5 p3 p1 p7 p0 p6 : Prop)
theorem file56_88755 : (((((p5 ∨ p2) → (p2 ∧ p5)) → ((p6 ∧ p1) ∨ (p0 → True))) ∨ (((p3 → False) → False) → False)) ∨ ((((p0 → False) ∧ (True → False)) ∨ ((p7 ∨ p1) ∧ (p0 → False))) ∨ (((p3 → False) ∧ (p6 ∧ False)) ∨ ((p1 ∧ p0) ∨ (p2 → True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  apply True.intro


variable (p3 p1 p5 p2 p0 : Prop)
theorem file56_89138 : ((((((False → p5) ∧ (p0 ∨ p1)) ∧ ((True → False) → (p1 ∧ p2))) → False) ∧ ((((p3 → True) → (p5 → p5)) ∧ ((p0 ∧ p3) → (p0 ∧ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p3 → True) → (p5 → p5)) ∧ ((p0 ∧ p3) → (p0 ∧ True))) := by
      apply And.intro
      intro assump_9
      intro assump_10
      exact assump_10
      intro assump_15
      apply And.intro
      cases assump_15
      case intro assump_16 assump_17 =>
        exact assump_16
      apply True.intro
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p6 p1 p7 p2 p0 : Prop)
theorem file56_89811 : ((((((p0 → False) → False) → ((p0 ∧ p7) ∧ (p6 → False))) → False) ∧ ((((False ∧ p0) → False) → False) ∧ (((p2 ∧ True) ∨ (p0 ∨ p1)) ∧ ((True → False) ∧ (p7 ∧ False))))) → False) := by
  intro assump_233
  cases assump_233
  case intro assump_234 assump_235 =>
    cases assump_235
    case intro assump_238 assump_239 =>
      cases assump_239
      case intro assump_242 assump_243 =>
        cases assump_242
        case inl assump_244 =>
          cases assump_244
          case intro assump_246 assump_247 =>
            cases assump_243
            case intro assump_252 assump_253 =>
              cases assump_253
              case intro assump_256 assump_257 =>
                apply False.elim assump_257
        case inr assump_245 =>
          cases assump_245
          case inl assump_262 =>
            cases assump_243
            case intro assump_266 assump_267 =>
              cases assump_267
              case intro assump_270 assump_271 =>
                apply False.elim assump_271
          case inr assump_263 =>
            cases assump_243
            case intro assump_278 assump_279 =>
              cases assump_279
              case intro assump_282 assump_283 =>
                apply False.elim assump_283


