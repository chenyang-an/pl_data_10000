variable (p4 p1 p5 p6 p0 p7 p2 : Prop)
theorem file84_47 : (((((p7 → False) ∨ (p1 → p2)) → ((p7 → p1) ∧ (p1 ∨ p1))) → (((True → p7) ∧ (p5 → p0)) ∨ ((p0 → False) → (p7 → p1)))) → ((((True → p7) → False) → ((p6 → p0) → (p6 ∨ True))) ∨ (((p4 → False) ∧ (p4 ∧ p5)) ∧ ((False → False) ∧ (p6 ∨ p1))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply Or.inr
  apply True.intro


variable (p6 p5 p2 p0 : Prop)
theorem file84_444 : ((((((p2 → p5) → (p6 ∧ p5)) → False) → (((False → False) ∧ (True ∨ p6)) ∨ ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → p5) → (p6 ∧ p5)) → False) → (((False → False) ∧ (True ∨ p6)) ∨ ((p0 → False) → False))) := by
    intro assump_5
    apply Or.inl
    apply And.intro
    intro assump_8
    apply False.elim assump_8
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p2 p5 p0 p4 p3 p7 : Prop)
theorem file84_977 : ((((((p4 ∨ True) ∨ (p2 ∧ p3)) → ((p0 → p0) → (False → False))) ∨ (((p0 → p7) ∧ (True ∨ False)) ∧ ((p1 → False) ∨ (p5 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p4 ∨ True) ∨ (p2 ∧ p3)) → ((p0 → p0) → (False → False))) ∨ (((p0 → p7) ∧ (True ∨ False)) ∧ ((p1 → False) ∨ (p5 ∨ False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p3 p0 p2 p5 p6 p1 p4 : Prop)
theorem file84_1534 : (((((True ∧ p5) → False) ∧ ((p2 ∧ p0) → (p1 ∧ p2))) → False) → ((((p6 ∧ p7) → (p1 ∨ True)) ∨ ((p4 ∨ p5) ∨ (p0 → p5))) → (((p2 → p1) → False) → ((p3 → p7) → (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p0 p4 p3 p5 p7 : Prop)
theorem file84_1886 : (((((True → False) ∧ (p0 ∨ p3)) → ((p0 ∧ p7) ∧ (False ∧ False))) ∨ (((p7 → False) → (p7 ∨ p4)) ∨ ((p0 → False) ∨ (p7 ∧ p0)))) ∨ ((((p3 → True) → False) ∧ ((False → False) → False)) ∨ (((p5 ∧ False) → (True ∧ False)) → ((p7 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      exact assump_6
    case inr assump_7 =>
      have assump_77 : True := by
        apply True.intro
      let assump_13 := assump_2 assump_77
      apply False.elim assump_13
  cases assump_1
  case intro assump_17 assump_18 =>
    cases assump_18
    case inl assump_21 =>
      have assump_78 : True := by
        apply True.intro
      let assump_26 := assump_17 assump_78
      apply False.elim assump_26
    case inr assump_22 =>
      have assump_79 : True := by
        apply True.intro
      let assump_33 := assump_17 assump_79
      apply False.elim assump_33
  apply And.intro
  cases assump_1
  case intro assump_37 assump_38 =>
    cases assump_38
    case inl assump_41 =>
      have assump_80 : True := by
        apply True.intro
      let assump_46 := assump_37 assump_80
      apply False.elim assump_46
    case inr assump_42 =>
      have assump_81 : True := by
        apply True.intro
      let assump_53 := assump_37 assump_81
      apply False.elim assump_53
  cases assump_1
  case intro assump_57 assump_58 =>
    cases assump_58
    case inl assump_61 =>
      have assump_82 : True := by
        apply True.intro
      let assump_66 := assump_57 assump_82
      apply False.elim assump_66
    case inr assump_62 =>
      have assump_83 : True := by
        apply True.intro
      let assump_73 := assump_57 assump_83
      apply False.elim assump_73


variable (p6 p4 p1 p3 p2 p7 p0 : Prop)
theorem file84_3760 : ((((((p0 ∧ False) ∧ (p7 ∧ p2)) → False) ∧ (((False → p0) ∧ (p7 → p3)) → False)) ∧ ((((True ∨ True) → (True ∧ p6)) ∧ ((p1 → p4) ∨ (p1 → p4))) ∧ (((p6 ∧ p0) ∧ (True → False)) ∧ ((False ∨ p1) → (True → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            cases assump_11
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  have assump_60 : True := by
                    apply True.intro
                  let assump_35 := assump_23 assump_60
                  apply False.elim assump_35
          case inr assump_17 =>
            cases assump_11
            case intro assump_41 assump_42 =>
              cases assump_41
              case intro assump_43 assump_44 =>
                cases assump_43
                case intro assump_45 assump_46 =>
                  have assump_61 : True := by
                    apply True.intro
                  let assump_56 := assump_44 assump_61
                  apply False.elim assump_56


variable (p7 p4 p0 p5 p3 p1 : Prop)
theorem file84_5216 : (((((p0 ∨ p7) ∨ (p4 → False)) → ((p4 ∧ p4) ∨ (p1 → p5))) ∧ (((p3 ∧ False) ∨ (False → p7)) → False)) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    have assump_29 : ((p3 ∧ False) ∨ (False → p7)) := by
      apply Or.inr
      intro assump_23
      apply False.elim assump_23
    let assump_22 := assump_17 assump_29
    apply False.elim assump_22


variable (p3 p2 p6 p4 p7 p0 p1 p5 : Prop)
theorem file84_5672 : ((((((False → False) ∨ (p5 ∨ p2)) ∧ ((True → False) → False)) → (((p2 → p4) ∨ (True → p2)) ∨ ((p5 → p5) → (p2 → False)))) ∧ ((((p7 → p6) ∧ (p3 ∨ p4)) → ((True ∨ p3) ∨ (p1 → True))) → (((p4 ∧ p4) → False) ∧ ((p1 → p0) ∧ (p0 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_29 : (((p7 → p6) ∧ (p3 ∨ p4)) → ((True ∨ p3) ∨ (p1 → True))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
    let assump_8 := assump_3 assump_29
    let assump_20 := And.right assump_8
    let assump_22 := And.right assump_20
    let assump_24 := And.right assump_22
    apply False.elim assump_24


variable (p0 p7 p4 p2 p3 p1 p5 : Prop)
theorem file84_6641 : (((((p0 → p5) → False) ∨ ((p3 → p2) ∨ (p0 → False))) ∧ (((p3 → p7) ∨ (False → True)) ∧ ((p5 → False) ∧ (p0 → p7)))) → ((((False ∧ p1) → False) → ((p4 ∧ False) → False)) ∨ (((p7 → False) → (p4 ∨ p0)) ∧ ((False ∨ p4) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply Or.inl
            intro assump_20
            intro assump_21
            cases assump_21
            case intro assump_22 assump_23 =>
              apply False.elim assump_23
        case inr assump_11 =>
          cases assump_9
          case intro assump_30 assump_31 =>
            apply Or.inl
            intro assump_36
            intro assump_37
            cases assump_37
            case intro assump_38 assump_39 =>
              apply False.elim assump_39
    case inr assump_5 =>
      cases assump_5
      case inl assump_44 =>
        cases assump_3
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_49
            case intro assump_54 assump_55 =>
              apply Or.inl
              intro assump_60
              intro assump_61
              cases assump_61
              case intro assump_62 assump_63 =>
                apply False.elim assump_63
          case inr assump_51 =>
            cases assump_49
            case intro assump_70 assump_71 =>
              apply Or.inl
              intro assump_76
              intro assump_77
              cases assump_77
              case intro assump_78 assump_79 =>
                apply False.elim assump_79
      case inr assump_45 =>
        cases assump_3
        case intro assump_86 assump_87 =>
          cases assump_86
          case inl assump_88 =>
            cases assump_87
            case intro assump_92 assump_93 =>
              apply Or.inl
              intro assump_98
              intro assump_99
              cases assump_99
              case intro assump_100 assump_101 =>
                apply False.elim assump_101
          case inr assump_89 =>
            cases assump_87
            case intro assump_108 assump_109 =>
              apply Or.inl
              intro assump_114
              intro assump_115
              cases assump_115
              case intro assump_116 assump_117 =>
                apply False.elim assump_117


variable (p3 p0 p6 p5 p4 p7 p2 : Prop)
theorem file84_9272 : (((((p7 ∧ p0) → (p5 ∧ p3)) → False) ∧ (((p0 ∨ p2) → (p5 → p6)) ∨ ((True → False) → (p6 ∨ p4)))) → ((((False ∧ p6) ∧ (p7 → p4)) ∧ ((p4 → p6) ∨ (p2 ∨ p5))) → (((False ∧ False) → (p2 ∨ p7)) → ((p6 ∨ p7) ∧ (p5 → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  intro assump_14
  apply True.intro


variable (p5 p0 p6 p2 p3 p1 p7 p4 : Prop)
theorem file84_9870 : (((((p4 → False) → False) ∧ ((p6 ∧ True) ∨ (p4 ∨ p2))) → (((p7 → p7) ∧ (True → False)) ∨ ((p0 → p2) ∨ (p4 → False)))) → ((((p5 ∨ True) ∧ (False ∧ True)) → ((p2 ∨ p3) → (p1 ∨ p4))) ∧ (((p2 → p6) → (p2 → p6)) ∨ ((p7 → p1) ∧ (p2 ∧ True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
      case inr assump_11 =>
        cases assump_9
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
  case inr assump_5 =>
    cases assump_2
    case intro assump_26 assump_27 =>
      cases assump_26
      case inl assump_28 =>
        cases assump_27
        case intro assump_32 assump_33 =>
          apply False.elim assump_32
      case inr assump_29 =>
        cases assump_27
        case intro assump_38 assump_39 =>
          apply False.elim assump_38
  apply Or.inl
  intro assump_44
  intro assump_45
  have assump_52 : p2 := by
    exact assump_45
  let assump_50 := assump_44 assump_52
  exact assump_50


variable (p2 p4 p7 p3 p1 p6 p5 p0 : Prop)
theorem file84_11145 : (((((p2 → False) ∧ (p1 → False)) → False) ∧ (((p6 → False) → (False → p7)) → False)) → ((((p0 → p4) → (p6 → False)) ∨ ((False ∨ p1) ∨ (p5 → p4))) ∧ (((p6 → False) ∧ (p1 ∨ p3)) ∧ ((True → False) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_72 : ((p6 → False) → (False → p7)) := by
      intro assump_17
      intro assump_18
      apply False.elim assump_18
    let assump_16 := assump_3 assump_72
    apply False.elim assump_16
  apply And.intro
  apply And.intro
  intro assump_24
  cases assump_1
  case intro assump_27 assump_28 =>
    have assump_73 : ((p6 → False) → (False → p7)) := by
      intro assump_34
      intro assump_35
      apply False.elim assump_35
    let assump_33 := assump_28 assump_73
    apply False.elim assump_33
  cases assump_1
  case intro assump_41 assump_42 =>
    have assump_74 : ((p6 → False) → (False → p7)) := by
      intro assump_48
      intro assump_49
      apply False.elim assump_49
    let assump_47 := assump_42 assump_74
    apply False.elim assump_47
  intro assump_55
  cases assump_1
  case intro assump_58 assump_59 =>
    have assump_75 : ((p6 → False) → (False → p7)) := by
      intro assump_65
      intro assump_66
      apply False.elim assump_66
    let assump_64 := assump_59 assump_75
    apply False.elim assump_64


variable (p3 p6 p7 : Prop)
theorem file84_12603 : (((((True → False) → (p3 → p6)) → ((False ∧ p7) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : (((True → False) → (p3 → p6)) → ((False ∧ p7) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p7 p2 : Prop)
theorem file84_13024 : (((((p7 → p7) ∧ (p2 → True)) → False) → False) ∧ ((((p7 → True) → (p2 ∧ False)) ∧ ((p0 ∧ p0) → (False → False))) → False)) := by
  apply And.intro
  intro assump_1
  have assump_27 : ((p7 → p7) ∧ (p2 → True)) := by
    apply And.intro
    intro assump_5
    exact assump_5
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_28 : (p7 → True) := by
      intro assump_21
      apply True.intro
    let assump_20 := assump_13 assump_28
    let assump_22 := And.right assump_20
    apply False.elim assump_22


variable (p2 p7 p3 p1 p4 p0 p6 p5 : Prop)
theorem file84_13737 : (((((p6 ∧ False) → (p1 ∧ p0)) → False) → (((p2 → False) → (True ∨ p7)) → False)) ∧ ((((p7 ∧ p2) ∨ (p7 → True)) ∨ ((True ∨ p1) → (p0 ∧ p3))) ∧ (((p5 ∨ p4) ∨ (p3 ∨ p3)) ∨ ((p5 ∧ False) ∨ (p5 → p5))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  have assump_28 : ((p6 ∧ False) → (p1 ∧ p0)) := by
    intro assump_8
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
    cases assump_8
    case intro assump_15 assump_16 =>
      apply False.elim assump_16
  let assump_7 := assump_1 assump_28
  apply False.elim assump_7
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_24
  apply True.intro
  apply Or.inr
  apply Or.inr
  intro assump_25
  exact assump_25


variable (p6 p0 p5 p2 p7 p1 p3 p4 : Prop)
theorem file84_14546 : (((((False ∧ p1) ∧ (p7 → False)) ∧ ((p2 ∨ p4) → (True → p6))) → (((False ∨ p6) → False) ∨ ((p5 ∧ p2) ∧ (p0 ∧ True)))) ∨ ((((p7 → p1) → False) ∧ ((p0 ∧ p6) → False)) ∧ (((False → False) → (p6 ∧ p6)) ∨ ((p3 → False) → (p0 ∨ p3))))) := by
  apply Or.inl
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_16


variable (p7 p4 p3 p2 p0 p5 p1 : Prop)
theorem file84_15087 : (((((True → p4) ∨ (p5 → False)) → ((p5 ∧ p5) → False)) → (((p1 ∧ p1) → (p3 → p2)) → ((p3 → p7) → (p1 ∨ True)))) ∨ ((((True → p7) ∨ (False ∧ p0)) → False) → (((p4 → False) → (p1 → p1)) ∨ ((p2 → False) ∧ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inr
  apply True.intro


variable (p5 p0 p1 p4 p6 p3 p2 : Prop)
theorem file84_15475 : (((((p6 → False) → False) ∧ ((p0 ∨ p2) → (p5 → False))) ∨ (((p1 → False) → (True ∧ p5)) ∨ ((p5 → False) → False))) → ((((True → False) → (p4 → p1)) ∨ ((p3 → False) ∨ (False → p3))) ∨ (((p5 ∨ p5) ∧ (p5 → p5)) → False))) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply Or.inl
      apply Or.inl
      intro assump_14
      intro assump_15
      have assump_50 : True := by
        apply True.intro
      let assump_20 := assump_14 assump_50
      apply False.elim assump_20
  case inr assump_7 =>
    cases assump_7
    case inl assump_24 =>
      apply Or.inl
      apply Or.inl
      intro assump_28
      intro assump_29
      have assump_51 : True := by
        apply True.intro
      let assump_34 := assump_28 assump_51
      apply False.elim assump_34
    case inr assump_25 =>
      apply Or.inl
      apply Or.inl
      intro assump_40
      intro assump_41
      have assump_52 : True := by
        apply True.intro
      let assump_46 := assump_40 assump_52
      apply False.elim assump_46


variable (p0 p6 p2 p7 p5 : Prop)
theorem file84_16614 : (((((p7 ∨ False) → (p7 ∨ p7)) ∨ ((p2 → False) ∧ (p6 → False))) → False) → ((((p7 → p5) ∧ (True → False)) → ((p2 ∨ p2) ∧ (False ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_18 : (((p7 ∨ False) → (p7 ∨ p7)) ∨ ((p2 → False) ∧ (p6 → False))) := by
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      apply Or.inl
      exact assump_9
    case inr assump_10 =>
      apply False.elim assump_10
  let assump_7 := assump_1 assump_18
  apply False.elim assump_7


variable (p1 p6 p2 : Prop)
theorem file84_17180 : (((((True → p2) ∧ (p2 → p6)) → ((True ∨ True) ∨ (p6 → p1))) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → p2) ∧ (p2 → p6)) → ((True ∨ True) ∨ (p6 → p1))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p3 p2 p5 p7 p6 p4 p0 : Prop)
theorem file84_17630 : (((((True → True) ∧ (p0 ∧ False)) ∧ ((p6 ∨ p2) → (p3 ∧ p1))) → (((p5 → False) ∧ (p5 ∨ p6)) ∧ ((True → False) → (p6 ∧ p0)))) ∨ ((((p3 ∨ p6) ∧ (p2 → False)) ∨ ((p4 ∧ p4) → (p6 → False))) → (((p6 → p1) → (p7 ∨ p4)) ∨ ((p7 ∨ True) ∧ (True → p7))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  cases assump_1
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply False.elim assump_24
  intro assump_29
  apply And.intro
  cases assump_1
  case intro assump_32 assump_33 =>
    cases assump_32
    case intro assump_34 assump_35 =>
      cases assump_35
      case intro assump_38 assump_39 =>
        apply False.elim assump_39
  cases assump_1
  case intro assump_46 assump_47 =>
    cases assump_46
    case intro assump_48 assump_49 =>
      cases assump_49
      case intro assump_52 assump_53 =>
        apply False.elim assump_53


variable (p6 p2 p7 p5 p0 p3 p4 : Prop)
theorem file84_18891 : (((((p3 ∨ p2) → (p5 → p7)) → ((p7 ∧ False) → (p4 → False))) → (((False → p6) → False) ∧ ((p0 ∧ p7) ∧ (False ∨ p6)))) → False) := by
  intro assump_1
  have assump_24 : (((p3 ∨ p2) → (p5 → p7)) → ((p7 ∧ False) → (p4 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_24
  let assump_16 := And.left assump_4
  have assump_25 : (False → p6) := by
    intro assump_18
    apply False.elim assump_18
  let assump_17 := assump_16 assump_25
  apply False.elim assump_17


variable (p7 p1 p2 p3 p5 p6 p4 : Prop)
theorem file84_19564 : (((((p6 ∧ p3) → (p4 → False)) → ((p3 ∨ p1) → False)) ∧ (((False ∨ p7) ∨ (p7 ∨ p2)) → False)) → ((((p5 → False) → (True ∨ p6)) ∨ ((True ∧ p2) ∨ (p1 → False))) ∨ (((p2 → p4) ∧ (p1 → p6)) → ((True → p2) ∨ (p1 → p7))))) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    apply Or.inl
    apply Or.inl
    intro assump_25
    apply Or.inl
    apply True.intro


variable (p0 p1 p2 : Prop)
theorem file84_20001 : ((((((p1 ∨ p0) ∨ (True ∨ False)) ∨ ((True → False) → False)) ∨ (((p2 → False) → False) ∧ ((p0 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p1 ∨ p0) ∨ (True ∨ False)) ∨ ((True → False) → False)) ∨ (((p2 → False) → False) ∧ ((p0 ∧ False) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p0 p7 p6 p5 p4 : Prop)
theorem file84_20502 : ((((((p7 → p4) → False) → ((p4 → False) → False)) → False) ∧ ((((p6 ∧ False) ∧ (True ∧ p5)) → False) ∧ (((p5 ∧ False) → (p0 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_26 : ((p5 ∧ False) → (p0 → False)) := by
        intro assump_13
        intro assump_14
        cases assump_13
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      let assump_12 := assump_7 assump_26
      apply False.elim assump_12


variable (p5 p1 p0 : Prop)
theorem file84_21121 : (((((p5 → p1) → (p1 ∨ p0)) → False) ∧ (((True → False) → False) ∧ ((False → p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : (False → p1) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p1 p0 p6 p2 p5 p4 : Prop)
theorem file84_21586 : (((((p4 → False) ∨ (p4 → False)) → ((True ∧ p2) → (True ∨ p5))) ∨ (((p4 ∧ p0) → (p1 ∨ p6)) ∨ ((p5 ∨ p1) → (p2 → False)))) ∨ ((((True → False) ∧ (p4 ∨ p2)) ∧ ((p4 → False) ∨ (p2 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_9
    case inl assump_17 =>
      apply Or.inl
      apply True.intro
    case inr assump_18 =>
      apply Or.inl
      apply True.intro


variable (p7 p2 p3 p5 p6 p1 p4 : Prop)
theorem file84_22127 : ((((((False ∧ p4) → False) ∨ ((p7 ∧ p2) ∨ (p4 → False))) ∨ (((p2 → p1) ∧ (p3 ∧ p2)) ∨ ((p5 ∨ p5) → (p3 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p4) → False) ∨ ((p7 ∧ p2) ∨ (p4 → False))) ∨ (((p2 → p1) ∧ (p3 ∧ p2)) ∨ ((p5 ∨ p5) → (p3 ∨ p6)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p3 p4 p0 : Prop)
theorem file84_22674 : ((((((False → False) ∨ (p0 ∧ p6)) ∨ ((p3 → False) ∧ (p0 → p3))) ∨ (((p4 → p6) → (False → False)) → ((p4 → p3) ∧ (p3 → False)))) → False) → False) := by
  intro assump_10
  have assump_20 : ((((False → False) ∨ (p0 ∧ p6)) ∨ ((p3 → False) ∧ (p0 → p3))) ∨ (((p4 → p6) → (False → False)) → ((p4 → p3) ∧ (p3 → False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_14
    apply False.elim assump_14
  let assump_13 := assump_10 assump_20
  apply False.elim assump_13


variable (p1 p2 p0 p6 p4 p3 p7 p5 : Prop)
theorem file84_23231 : (((((p7 ∧ p5) ∨ (p7 ∧ p4)) → ((p7 ∨ p1) ∨ (p5 ∧ True))) → (((p3 → p6) ∨ (p6 → p2)) → ((p5 → p5) ∨ (p6 ∧ p1)))) ∨ ((((True ∨ False) → False) → False) → (((True → p5) ∨ (p5 ∨ p0)) ∨ ((p6 ∧ p1) ∧ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    exact assump_9
  case inr assump_4 =>
    apply Or.inl
    intro assump_16
    exact assump_16


variable (p5 p7 p4 p3 p0 p2 p6 p1 : Prop)
theorem file84_23737 : (((((p0 → p2) ∧ (p5 ∨ p6)) ∧ ((False ∧ p6) ∧ (p2 ∧ p4))) → (((p3 → False) ∨ (p1 ∧ p5)) ∧ ((p7 ∨ p5) → (False → False)))) ∨ ((((p5 → p6) → (p4 → p0)) → ((p3 ∨ p3) → (p0 ∧ p5))) → False)) := by
  apply Or.inl
  intro assump_5
  apply And.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        cases assump_7
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
      case inr assump_13 =>
        cases assump_7
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            apply False.elim assump_26
  intro assump_30
  intro assump_31
  apply False.elim assump_31


variable (p5 p7 p6 : Prop)
theorem file84_24626 : (((((p7 → False) → False) → ((p5 ∧ p6) ∨ (True → True))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p7 → False) → False) → ((p5 ∧ p6) ∨ (True → True))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p3 p0 p7 p4 p2 p5 : Prop)
theorem file84_25008 : ((((((p5 → p6) ∧ (p7 → False)) ∧ ((True → p2) ∨ (p6 → p3))) ∨ (((True → False) → (p4 → False)) → False)) ∧ ((((p4 ∨ p6) ∧ (p0 → False)) ∨ ((True ∨ True) ∨ (p6 → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case inl assump_14 =>
            have assump_40 : (((p4 ∨ p6) ∧ (p0 → False)) ∨ ((True ∨ True) ∨ (p6 → p3))) := by
              apply Or.inr
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_20 := assump_3 assump_40
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_41 : (((p4 ∨ p6) ∧ (p0 → False)) ∨ ((True ∨ True) ∨ (p6 → p3))) := by
              apply Or.inr
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_28 := assump_3 assump_41
            apply False.elim assump_28
    case inr assump_5 =>
      have assump_42 : (((p4 ∨ p6) ∧ (p0 → False)) ∨ ((True ∨ True) ∨ (p6 → p3))) := by
        apply Or.inr
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_36 := assump_3 assump_42
      apply False.elim assump_36


variable (p6 p5 p4 p1 p0 p2 p7 : Prop)
theorem file84_26448 : (((((p2 → False) → (p4 ∨ p5)) ∨ ((p5 → False) ∨ (True → True))) ∧ (((p7 → p0) ∨ (False ∨ p4)) ∧ ((False ∨ p0) ∧ (True → False)))) → ((((p4 ∧ p1) ∨ (p6 → False)) ∨ ((p4 ∧ p7) → (p4 ∨ p7))) → (((p0 → False) ∨ (p5 → p5)) ∨ ((p1 ∧ p0) ∨ (p7 ∧ p2))))) := by
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
          case inl assump_15 =>
            cases assump_14
            case intro assump_19 assump_20 =>
              cases assump_19
              case inl assump_21 =>
                cases assump_20
                case intro assump_25 assump_26 =>
                  cases assump_25
                  case inl assump_27 =>
                    apply False.elim assump_27
                  case inr assump_28 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_35
                    have assump_485 : True := by
                      apply True.intro
                    let assump_39 := assump_26 assump_485
                    apply False.elim assump_39
              case inr assump_22 =>
                cases assump_22
                case inl assump_43 =>
                  apply False.elim assump_43
                case inr assump_44 =>
                  cases assump_20
                  case intro assump_49 assump_50 =>
                    cases assump_49
                    case inl assump_51 =>
                      apply False.elim assump_51
                    case inr assump_52 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_59
                      have assump_486 : True := by
                        apply True.intro
                      let assump_63 := assump_50 assump_486
                      apply False.elim assump_63
          case inr assump_16 =>
            cases assump_16
            case inl assump_67 =>
              cases assump_14
              case intro assump_71 assump_72 =>
                cases assump_71
                case inl assump_73 =>
                  cases assump_72
                  case intro assump_77 assump_78 =>
                    cases assump_77
                    case inl assump_79 =>
                      apply False.elim assump_79
                    case inr assump_80 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_87
                      have assump_487 : True := by
                        apply True.intro
                      let assump_91 := assump_78 assump_487
                      apply False.elim assump_91
                case inr assump_74 =>
                  cases assump_74
                  case inl assump_95 =>
                    apply False.elim assump_95
                  case inr assump_96 =>
                    cases assump_72
                    case intro assump_101 assump_102 =>
                      cases assump_101
                      case inl assump_103 =>
                        apply False.elim assump_103
                      case inr assump_104 =>
                        apply Or.inl
                        apply Or.inl
                        intro assump_111
                        have assump_488 : True := by
                          apply True.intro
                        let assump_115 := assump_102 assump_488
                        apply False.elim assump_115
            case inr assump_68 =>
              cases assump_14
              case intro assump_121 assump_122 =>
                cases assump_121
                case inl assump_123 =>
                  cases assump_122
                  case intro assump_127 assump_128 =>
                    cases assump_127
                    case inl assump_129 =>
                      apply False.elim assump_129
                    case inr assump_130 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_137
                      have assump_489 : True := by
                        apply True.intro
                      let assump_141 := assump_128 assump_489
                      apply False.elim assump_141
                case inr assump_124 =>
                  cases assump_124
                  case inl assump_145 =>
                    apply False.elim assump_145
                  case inr assump_146 =>
                    cases assump_122
                    case intro assump_151 assump_152 =>
                      cases assump_151
                      case inl assump_153 =>
                        apply False.elim assump_153
                      case inr assump_154 =>
                        apply Or.inl
                        apply Or.inl
                        intro assump_161
                        have assump_490 : True := by
                          apply True.intro
                        let assump_165 := assump_152 assump_490
                        apply False.elim assump_165
    case inr assump_6 =>
      cases assump_1
      case intro assump_171 assump_172 =>
        cases assump_171
        case inl assump_173 =>
          cases assump_172
          case intro assump_177 assump_178 =>
            cases assump_177
            case inl assump_179 =>
              cases assump_178
              case intro assump_183 assump_184 =>
                cases assump_183
                case inl assump_185 =>
                  apply False.elim assump_185
                case inr assump_186 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_193
                  have assump_491 : True := by
                    apply True.intro
                  let assump_197 := assump_184 assump_491
                  apply False.elim assump_197
            case inr assump_180 =>
              cases assump_180
              case inl assump_201 =>
                apply False.elim assump_201
              case inr assump_202 =>
                cases assump_178
                case intro assump_207 assump_208 =>
                  cases assump_207
                  case inl assump_209 =>
                    apply False.elim assump_209
                  case inr assump_210 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_217
                    have assump_492 : True := by
                      apply True.intro
                    let assump_221 := assump_208 assump_492
                    apply False.elim assump_221
        case inr assump_174 =>
          cases assump_174
          case inl assump_225 =>
            cases assump_172
            case intro assump_229 assump_230 =>
              cases assump_229
              case inl assump_231 =>
                cases assump_230
                case intro assump_235 assump_236 =>
                  cases assump_235
                  case inl assump_237 =>
                    apply False.elim assump_237
                  case inr assump_238 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_245
                    have assump_493 : True := by
                      apply True.intro
                    let assump_249 := assump_236 assump_493
                    apply False.elim assump_249
              case inr assump_232 =>
                cases assump_232
                case inl assump_253 =>
                  apply False.elim assump_253
                case inr assump_254 =>
                  cases assump_230
                  case intro assump_259 assump_260 =>
                    cases assump_259
                    case inl assump_261 =>
                      apply False.elim assump_261
                    case inr assump_262 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_269
                      have assump_494 : True := by
                        apply True.intro
                      let assump_273 := assump_260 assump_494
                      apply False.elim assump_273
          case inr assump_226 =>
            cases assump_172
            case intro assump_279 assump_280 =>
              cases assump_279
              case inl assump_281 =>
                cases assump_280
                case intro assump_285 assump_286 =>
                  cases assump_285
                  case inl assump_287 =>
                    apply False.elim assump_287
                  case inr assump_288 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_295
                    have assump_495 : True := by
                      apply True.intro
                    let assump_299 := assump_286 assump_495
                    apply False.elim assump_299
              case inr assump_282 =>
                cases assump_282
                case inl assump_303 =>
                  apply False.elim assump_303
                case inr assump_304 =>
                  cases assump_280
                  case intro assump_309 assump_310 =>
                    cases assump_309
                    case inl assump_311 =>
                      apply False.elim assump_311
                    case inr assump_312 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_319
                      have assump_496 : True := by
                        apply True.intro
                      let assump_323 := assump_310 assump_496
                      apply False.elim assump_323
  case inr assump_4 =>
    cases assump_1
    case intro assump_329 assump_330 =>
      cases assump_329
      case inl assump_331 =>
        cases assump_330
        case intro assump_335 assump_336 =>
          cases assump_335
          case inl assump_337 =>
            cases assump_336
            case intro assump_341 assump_342 =>
              cases assump_341
              case inl assump_343 =>
                apply False.elim assump_343
              case inr assump_344 =>
                apply Or.inl
                apply Or.inl
                intro assump_351
                have assump_497 : True := by
                  apply True.intro
                let assump_355 := assump_342 assump_497
                apply False.elim assump_355
          case inr assump_338 =>
            cases assump_338
            case inl assump_359 =>
              apply False.elim assump_359
            case inr assump_360 =>
              cases assump_336
              case intro assump_365 assump_366 =>
                cases assump_365
                case inl assump_367 =>
                  apply False.elim assump_367
                case inr assump_368 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_375
                  have assump_498 : True := by
                    apply True.intro
                  let assump_379 := assump_366 assump_498
                  apply False.elim assump_379
      case inr assump_332 =>
        cases assump_332
        case inl assump_383 =>
          cases assump_330
          case intro assump_387 assump_388 =>
            cases assump_387
            case inl assump_389 =>
              cases assump_388
              case intro assump_393 assump_394 =>
                cases assump_393
                case inl assump_395 =>
                  apply False.elim assump_395
                case inr assump_396 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_403
                  have assump_499 : True := by
                    apply True.intro
                  let assump_407 := assump_394 assump_499
                  apply False.elim assump_407
            case inr assump_390 =>
              cases assump_390
              case inl assump_411 =>
                apply False.elim assump_411
              case inr assump_412 =>
                cases assump_388
                case intro assump_417 assump_418 =>
                  cases assump_417
                  case inl assump_419 =>
                    apply False.elim assump_419
                  case inr assump_420 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_427
                    have assump_500 : True := by
                      apply True.intro
                    let assump_431 := assump_418 assump_500
                    apply False.elim assump_431
        case inr assump_384 =>
          cases assump_330
          case intro assump_437 assump_438 =>
            cases assump_437
            case inl assump_439 =>
              cases assump_438
              case intro assump_443 assump_444 =>
                cases assump_443
                case inl assump_445 =>
                  apply False.elim assump_445
                case inr assump_446 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_453
                  have assump_501 : True := by
                    apply True.intro
                  let assump_457 := assump_444 assump_501
                  apply False.elim assump_457
            case inr assump_440 =>
              cases assump_440
              case inl assump_461 =>
                apply False.elim assump_461
              case inr assump_462 =>
                cases assump_438
                case intro assump_467 assump_468 =>
                  cases assump_467
                  case inl assump_469 =>
                    apply False.elim assump_469
                  case inr assump_470 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_477
                    have assump_502 : True := by
                      apply True.intro
                    let assump_481 := assump_468 assump_502
                    apply False.elim assump_481


variable (p0 p2 p3 p1 : Prop)
theorem file84_40603 : ((((((p2 ∨ p0) → False) ∧ ((False ∧ False) ∧ (p3 → p1))) → (((True ∨ p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p2 ∨ p0) → False) ∧ ((False ∧ False) ∧ (p3 → p1))) → (((True ∨ p1) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p5 p7 p3 p4 p1 p6 p0 : Prop)
theorem file84_41238 : (((((p4 ∨ True) → (True ∧ False)) ∧ ((False ∨ p3) ∧ (p1 ∧ p7))) → False) ∨ ((((p4 ∧ True) ∧ (p3 ∨ p0)) ∨ ((p3 ∧ False) → False)) ∨ (((p1 ∨ p5) ∧ (p6 ∧ p6)) ∨ ((p0 → True) → (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          have assump_29 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_23 := assump_2 assump_29
          let assump_24 := And.right assump_23
          apply False.elim assump_24


variable (p0 p3 p1 p5 p4 p7 : Prop)
theorem file84_42035 : (((((p4 → False) ∨ (p7 → False)) → ((p5 ∨ True) ∨ (p7 ∨ p4))) → False) → ((((p3 ∨ p3) ∨ (p0 ∧ p0)) → False) ∨ (((p5 → False) ∨ (p7 ∨ p1)) ∨ ((p7 ∧ p0) ∧ (p0 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      have assump_56 : (((p4 → False) ∨ (p7 → False)) → ((p5 ∨ True) ∨ (p7 ∨ p4))) := by
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      let assump_12 := assump_1 assump_56
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_57 : (((p4 → False) ∨ (p7 → False)) → ((p5 ∨ True) ∨ (p7 ∨ p4))) := by
        intro assump_27
        cases assump_27
        case inl assump_28 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_29 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      let assump_26 := assump_1 assump_57
      apply False.elim assump_26
  case inr assump_6 =>
    cases assump_6
    case intro assump_37 assump_38 =>
      have assump_58 : (((p4 → False) ∨ (p7 → False)) → ((p5 ∨ True) ∨ (p7 ∨ p4))) := by
        intro assump_46
        cases assump_46
        case inl assump_47 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_48 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      let assump_45 := assump_1 assump_58
      apply False.elim assump_45


variable (p1 p6 p4 p5 p7 p2 p3 : Prop)
theorem file84_43766 : (((((p5 ∧ p1) → (p7 ∨ p1)) ∧ ((False ∧ True) ∧ (p7 ∧ p4))) ∧ (((p3 → False) ∨ (p4 → p6)) ∨ ((p2 ∨ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p3 p5 p6 p4 p2 p7 p0 : Prop)
theorem file84_44241 : ((((((p0 ∨ p0) → False) ∧ ((p3 ∧ p0) → (p5 → p6))) ∨ (((p7 → False) → False) ∨ ((p3 → p4) → (p2 ∨ p3)))) ∧ ((((p0 → False) ∧ (p4 ∨ p2)) ∧ ((p6 → False) ∨ (p2 → p0))) ∧ (((p6 ∧ p7) ∧ (p6 ∧ p0)) ∨ ((p7 → True) ∧ (p0 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_17
              case inl assump_20 =>
                cases assump_15
                case inl assump_24 =>
                  cases assump_13
                  case inl assump_28 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_30
                      case intro assump_32 assump_33 =>
                        cases assump_31
                        case intro assump_38 assump_39 =>
                          have assump_519 : p6 := by
                            exact assump_38
                          let assump_48 := assump_24 assump_519
                          apply False.elim assump_48
                  case inr assump_29 =>
                    cases assump_29
                    case intro assump_52 assump_53 =>
                      cases assump_53
                      case intro assump_56 assump_57 =>
                        apply False.elim assump_57
                case inr assump_25 =>
                  cases assump_13
                  case inl assump_64 =>
                    cases assump_64
                    case intro assump_66 assump_67 =>
                      cases assump_66
                      case intro assump_68 assump_69 =>
                        cases assump_67
                        case intro assump_74 assump_75 =>
                          have assump_520 : p0 := by
                            exact assump_75
                          let assump_86 := assump_16 assump_520
                          apply False.elim assump_86
                  case inr assump_65 =>
                    cases assump_65
                    case intro assump_90 assump_91 =>
                      cases assump_91
                      case intro assump_94 assump_95 =>
                        apply False.elim assump_95
              case inr assump_21 =>
                cases assump_15
                case inl assump_102 =>
                  cases assump_13
                  case inl assump_106 =>
                    cases assump_106
                    case intro assump_108 assump_109 =>
                      cases assump_108
                      case intro assump_110 assump_111 =>
                        cases assump_109
                        case intro assump_116 assump_117 =>
                          have assump_521 : p6 := by
                            exact assump_116
                          let assump_126 := assump_102 assump_521
                          apply False.elim assump_126
                  case inr assump_107 =>
                    cases assump_107
                    case intro assump_130 assump_131 =>
                      cases assump_131
                      case intro assump_134 assump_135 =>
                        apply False.elim assump_135
                case inr assump_103 =>
                  cases assump_13
                  case inl assump_142 =>
                    cases assump_142
                    case intro assump_144 assump_145 =>
                      cases assump_144
                      case intro assump_146 assump_147 =>
                        cases assump_145
                        case intro assump_152 assump_153 =>
                          have assump_522 : p0 := by
                            exact assump_153
                          let assump_165 := assump_16 assump_522
                          apply False.elim assump_165
                  case inr assump_143 =>
                    cases assump_143
                    case intro assump_169 assump_170 =>
                      cases assump_170
                      case intro assump_173 assump_174 =>
                        apply False.elim assump_174
    case inr assump_5 =>
      cases assump_5
      case inl assump_179 =>
        cases assump_3
        case intro assump_183 assump_184 =>
          cases assump_183
          case intro assump_185 assump_186 =>
            cases assump_185
            case intro assump_187 assump_188 =>
              cases assump_188
              case inl assump_191 =>
                cases assump_186
                case inl assump_195 =>
                  cases assump_184
                  case inl assump_199 =>
                    cases assump_199
                    case intro assump_201 assump_202 =>
                      cases assump_201
                      case intro assump_203 assump_204 =>
                        cases assump_202
                        case intro assump_209 assump_210 =>
                          have assump_523 : p6 := by
                            exact assump_209
                          let assump_219 := assump_195 assump_523
                          apply False.elim assump_219
                  case inr assump_200 =>
                    cases assump_200
                    case intro assump_223 assump_224 =>
                      cases assump_224
                      case intro assump_227 assump_228 =>
                        apply False.elim assump_228
                case inr assump_196 =>
                  cases assump_184
                  case inl assump_235 =>
                    cases assump_235
                    case intro assump_237 assump_238 =>
                      cases assump_237
                      case intro assump_239 assump_240 =>
                        cases assump_238
                        case intro assump_245 assump_246 =>
                          have assump_524 : p0 := by
                            exact assump_246
                          let assump_257 := assump_187 assump_524
                          apply False.elim assump_257
                  case inr assump_236 =>
                    cases assump_236
                    case intro assump_261 assump_262 =>
                      cases assump_262
                      case intro assump_265 assump_266 =>
                        apply False.elim assump_266
              case inr assump_192 =>
                cases assump_186
                case inl assump_273 =>
                  cases assump_184
                  case inl assump_277 =>
                    cases assump_277
                    case intro assump_279 assump_280 =>
                      cases assump_279
                      case intro assump_281 assump_282 =>
                        cases assump_280
                        case intro assump_287 assump_288 =>
                          have assump_525 : p6 := by
                            exact assump_287
                          let assump_297 := assump_273 assump_525
                          apply False.elim assump_297
                  case inr assump_278 =>
                    cases assump_278
                    case intro assump_301 assump_302 =>
                      cases assump_302
                      case intro assump_305 assump_306 =>
                        apply False.elim assump_306
                case inr assump_274 =>
                  cases assump_184
                  case inl assump_313 =>
                    cases assump_313
                    case intro assump_315 assump_316 =>
                      cases assump_315
                      case intro assump_317 assump_318 =>
                        cases assump_316
                        case intro assump_323 assump_324 =>
                          have assump_526 : p0 := by
                            exact assump_324
                          let assump_336 := assump_187 assump_526
                          apply False.elim assump_336
                  case inr assump_314 =>
                    cases assump_314
                    case intro assump_340 assump_341 =>
                      cases assump_341
                      case intro assump_344 assump_345 =>
                        apply False.elim assump_345
      case inr assump_180 =>
        cases assump_3
        case intro assump_352 assump_353 =>
          cases assump_352
          case intro assump_354 assump_355 =>
            cases assump_354
            case intro assump_356 assump_357 =>
              cases assump_357
              case inl assump_360 =>
                cases assump_355
                case inl assump_364 =>
                  cases assump_353
                  case inl assump_368 =>
                    cases assump_368
                    case intro assump_370 assump_371 =>
                      cases assump_370
                      case intro assump_372 assump_373 =>
                        cases assump_371
                        case intro assump_378 assump_379 =>
                          have assump_527 : p6 := by
                            exact assump_378
                          let assump_388 := assump_364 assump_527
                          apply False.elim assump_388
                  case inr assump_369 =>
                    cases assump_369
                    case intro assump_392 assump_393 =>
                      cases assump_393
                      case intro assump_396 assump_397 =>
                        apply False.elim assump_397
                case inr assump_365 =>
                  cases assump_353
                  case inl assump_404 =>
                    cases assump_404
                    case intro assump_406 assump_407 =>
                      cases assump_406
                      case intro assump_408 assump_409 =>
                        cases assump_407
                        case intro assump_414 assump_415 =>
                          have assump_528 : p0 := by
                            exact assump_415
                          let assump_426 := assump_356 assump_528
                          apply False.elim assump_426
                  case inr assump_405 =>
                    cases assump_405
                    case intro assump_430 assump_431 =>
                      cases assump_431
                      case intro assump_434 assump_435 =>
                        apply False.elim assump_435
              case inr assump_361 =>
                cases assump_355
                case inl assump_442 =>
                  cases assump_353
                  case inl assump_446 =>
                    cases assump_446
                    case intro assump_448 assump_449 =>
                      cases assump_448
                      case intro assump_450 assump_451 =>
                        cases assump_449
                        case intro assump_456 assump_457 =>
                          have assump_529 : p6 := by
                            exact assump_456
                          let assump_466 := assump_442 assump_529
                          apply False.elim assump_466
                  case inr assump_447 =>
                    cases assump_447
                    case intro assump_470 assump_471 =>
                      cases assump_471
                      case intro assump_474 assump_475 =>
                        apply False.elim assump_475
                case inr assump_443 =>
                  cases assump_353
                  case inl assump_482 =>
                    cases assump_482
                    case intro assump_484 assump_485 =>
                      cases assump_484
                      case intro assump_486 assump_487 =>
                        cases assump_485
                        case intro assump_492 assump_493 =>
                          have assump_530 : p0 := by
                            exact assump_493
                          let assump_505 := assump_356 assump_530
                          apply False.elim assump_505
                  case inr assump_483 =>
                    cases assump_483
                    case intro assump_509 assump_510 =>
                      cases assump_510
                      case intro assump_513 assump_514 =>
                        apply False.elim assump_514


variable (p3 p1 p7 p2 p4 p0 p5 p6 : Prop)
theorem file84_56808 : (((((p2 → False) → False) → ((True ∧ p5) → False)) → (((p4 → False) ∨ (p5 ∧ p5)) → ((p1 ∨ p7) ∧ (p3 ∧ p3)))) → ((((p3 → False) → False) → ((p1 → False) ∨ (p6 → p1))) → (((p0 → True) ∧ (False ∨ p5)) → ((False ∧ p0) ∨ (p7 → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      apply False.elim assump_8
    case inr assump_9 =>
      apply Or.inr
      intro assump_18
      apply True.intro


variable (p5 p1 p3 p7 : Prop)
theorem file84_57367 : (((((p5 ∨ p1) → (p1 ∨ p5)) → False) → False) ∨ ((((p3 → p7) ∨ (False → p5)) → ((p3 ∧ p5) → False)) → False)) := by
  apply Or.inl
  intro assump_16
  have assump_30 : ((p5 ∨ p1) → (p1 ∨ p5)) := by
    intro assump_20
    cases assump_20
    case inl assump_21 =>
      apply Or.inr
      exact assump_21
    case inr assump_22 =>
      apply Or.inl
      exact assump_22
  let assump_19 := assump_16 assump_30
  apply False.elim assump_19


variable (p2 p7 p4 p5 : Prop)
theorem file84_57860 : ((((((p2 → False) ∧ (p5 → False)) ∨ ((p5 ∨ True) ∨ (False → p4))) → (((p2 → False) ∧ (False ∧ p7)) → False)) → False) → False) := by
  intro assump_5
  have assump_22 : ((((p2 → False) ∧ (p5 → False)) ∨ ((p5 ∨ True) ∨ (False → p4))) → (((p2 → False) ∧ (False ∧ p7)) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p6 p1 p5 p0 p2 : Prop)
theorem file84_58458 : (((((p5 ∨ False) → False) → ((False ∧ True) → (p0 ∨ False))) → (((p2 ∧ p1) ∧ (p1 ∧ False)) ∧ ((p5 → p0) → (p2 ∨ p6)))) → False) := by
  intro assump_1
  have assump_21 : (((p5 ∨ False) → False) → ((False ∧ True) → (p0 ∨ False))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_21
  let assump_11 := And.left assump_4
  let assump_12 := And.right assump_11
  let assump_16 := And.right assump_12
  apply False.elim assump_16


variable (p3 p6 p5 p7 p2 : Prop)
theorem file84_59056 : ((((((True → False) → False) ∨ ((p6 → p2) → False)) → False) ∧ ((((p7 → p3) → False) ∨ ((p7 ∧ p5) ∨ (True → p7))) ∧ (((p7 ∨ p3) → False) ∧ ((p2 ∧ p2) ∨ (p7 ∧ p7))))) → False) := by
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
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_133 : (p7 → p3) := by
                intro assump_28
                have assump_134 : (p7 ∨ p3) := by
                  apply Or.inl
                  exact assump_28
                let assump_34 := assump_12 assump_134
                apply False.elim assump_34
              let assump_27 := assump_8 assump_133
              apply False.elim assump_27
          case inr assump_17 =>
            cases assump_17
            case intro assump_41 assump_42 =>
              have assump_135 : (p7 ∨ p3) := by
                apply Or.inl
                exact assump_42
              let assump_49 := assump_12 assump_135
              apply False.elim assump_49
      case inr assump_9 =>
        cases assump_9
        case inl assump_53 =>
          cases assump_53
          case intro assump_55 assump_56 =>
            cases assump_7
            case intro assump_61 assump_62 =>
              cases assump_62
              case inl assump_65 =>
                cases assump_65
                case intro assump_67 assump_68 =>
                  have assump_136 : (p7 ∨ p3) := by
                    apply Or.inl
                    exact assump_55
                  let assump_75 := assump_61 assump_136
                  apply False.elim assump_75
              case inr assump_66 =>
                cases assump_66
                case intro assump_79 assump_80 =>
                  have assump_137 : (p7 ∨ p3) := by
                    apply Or.inl
                    exact assump_80
                  let assump_87 := assump_61 assump_137
                  apply False.elim assump_87
        case inr assump_54 =>
          cases assump_7
          case intro assump_93 assump_94 =>
            cases assump_94
            case inl assump_97 =>
              cases assump_97
              case intro assump_99 assump_100 =>
                have assump_138 : (((True → False) → False) ∨ ((p6 → p2) → False)) := by
                  apply Or.inl
                  intro assump_111
                  have assump_139 : True := by
                    apply True.intro
                  let assump_114 := assump_111 assump_139
                  apply False.elim assump_114
                let assump_110 := assump_2 assump_138
                apply False.elim assump_110
            case inr assump_98 =>
              cases assump_98
              case intro assump_121 assump_122 =>
                have assump_140 : (p7 ∨ p3) := by
                  apply Or.inl
                  exact assump_122
                let assump_129 := assump_93 assump_140
                apply False.elim assump_129


variable (p4 p2 p3 p7 p1 p0 : Prop)
theorem file84_62300 : (((((False ∨ p7) ∧ (False → False)) ∧ ((p1 ∨ p0) ∧ (True → False))) → False) ∨ ((((p3 → False) → (p0 ∨ p1)) ∨ ((p4 ∨ p2) ∨ (False ∧ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply False.elim assump_6
      case inr assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            have assump_34 : True := by
              apply True.intro
            let assump_22 := assump_15 assump_34
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_35 : True := by
              apply True.intro
            let assump_30 := assump_15 assump_35
            apply False.elim assump_30


variable (p4 p0 p5 p2 p3 p1 p6 p7 : Prop)
theorem file84_63240 : (((((p1 ∧ False) → False) ∨ ((False → False) ∨ (p3 → p5))) ∨ (((p5 → p0) → (p7 → p2)) ∨ ((p3 ∧ p7) → (p4 ∧ p4)))) ∨ ((((p0 → False) → (p6 → False)) ∨ ((p4 → False) ∨ (p5 ∨ p2))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p4 p0 p6 p3 p5 p7 p2 : Prop)
theorem file84_63640 : (((((p0 ∧ p6) ∧ (p3 ∧ p6)) ∧ ((p7 ∨ p7) → False)) → (((p4 → False) → False) ∨ ((p7 ∧ True) ∨ (p0 ∨ True)))) → ((((p2 → p5) → False) ∧ ((False ∨ False) ∧ (p3 ∧ p5))) → False)) := by
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
        apply False.elim assump_10


variable (p3 p1 p7 p2 p6 p4 : Prop)
theorem file84_64166 : (((((p7 ∧ p6) → False) → ((False ∨ p6) ∨ (p3 ∨ p2))) → False) → ((((False → True) ∨ (p4 → p7)) → ((p1 → False) → (False → p6))) ∨ (((True → p7) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p5 p2 p7 p3 p1 p6 p0 p4 : Prop)
theorem file84_64513 : (((((p7 ∨ p2) ∨ (p3 → True)) → False) → False) ∨ ((((p6 → p3) → (True ∧ True)) ∨ ((p5 → p2) ∧ (p1 → p5))) ∧ (((p6 ∨ p3) ∨ (p0 ∧ p2)) ∨ ((p4 ∧ p1) ∧ (True → p1))))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p7 ∨ p2) ∨ (p3 → True)) := by
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p3 p6 p7 p0 p5 p4 : Prop)
theorem file84_64946 : (((((p3 → p5) ∨ (p0 ∧ p7)) → ((False ∨ p0) ∨ (p6 ∨ True))) ∨ (((False → p6) → (True → p0)) ∧ ((p7 ∨ True) → False))) ∨ ((((p4 → p4) → (p7 → False)) → False) → (((p4 ∧ p0) ∨ (False → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inr
      exact assump_6


variable (p4 p0 p7 p5 p2 p6 : Prop)
theorem file84_65492 : (((((p7 → False) ∨ (p4 ∨ p4)) → ((p5 ∨ p0) ∨ (p5 → p7))) → False) → ((((p2 → p6) ∨ (p2 ∨ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_82 : (((p7 → False) ∨ (p4 ∨ p4)) → ((p5 ∨ p0) ∨ (p5 → p7))) := by
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      apply Or.inr
      intro assump_13
      have assump_83 : (((p7 → False) ∨ (p4 ∨ p4)) → ((p5 ∨ p0) ∨ (p5 → p7))) := by
        intro assump_19
        cases assump_19
        case inl assump_20 =>
          apply Or.inl
          apply Or.inl
          exact assump_13
        case inr assump_21 =>
          cases assump_21
          case inl assump_24 =>
            apply Or.inl
            apply Or.inl
            exact assump_13
          case inr assump_25 =>
            apply Or.inl
            apply Or.inl
            exact assump_13
      let assump_18 := assump_1 assump_83
      apply False.elim assump_18
    case inr assump_10 =>
      cases assump_10
      case inl assump_33 =>
        apply Or.inr
        intro assump_37
        have assump_84 : (((p7 → False) ∨ (p4 ∨ p4)) → ((p5 ∨ p0) ∨ (p5 → p7))) := by
          intro assump_43
          cases assump_43
          case inl assump_44 =>
            apply Or.inl
            apply Or.inl
            exact assump_37
          case inr assump_45 =>
            cases assump_45
            case inl assump_48 =>
              apply Or.inl
              apply Or.inl
              exact assump_37
            case inr assump_49 =>
              apply Or.inl
              apply Or.inl
              exact assump_37
        let assump_42 := assump_1 assump_84
        apply False.elim assump_42
      case inr assump_34 =>
        apply Or.inr
        intro assump_59
        have assump_85 : (((p7 → False) ∨ (p4 ∨ p4)) → ((p5 ∨ p0) ∨ (p5 → p7))) := by
          intro assump_65
          cases assump_65
          case inl assump_66 =>
            apply Or.inl
            apply Or.inl
            exact assump_59
          case inr assump_67 =>
            cases assump_67
            case inl assump_70 =>
              apply Or.inl
              apply Or.inl
              exact assump_59
            case inr assump_71 =>
              apply Or.inl
              apply Or.inl
              exact assump_59
        let assump_64 := assump_1 assump_85
        apply False.elim assump_64
  let assump_7 := assump_1 assump_82
  apply False.elim assump_7


variable (p0 p7 p6 p4 p1 p3 : Prop)
theorem file84_67979 : ((((((p7 ∧ p0) ∧ (False ∧ p3)) → ((p4 ∨ p6) → False)) ∨ (((p4 → False) ∨ (p6 → True)) ∧ ((p0 ∨ p1) ∧ (False → p7)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p7 ∧ p0) ∧ (False ∧ p3)) → ((p4 ∨ p6) → False)) ∨ (((p4 → False) ∨ (p6 → True)) ∧ ((p0 ∨ p1) ∧ (False → p7)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
    case inr assump_8 =>
      cases assump_5
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          cases assump_26
          case intro assump_33 assump_34 =>
            apply False.elim assump_33
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p2 p4 p1 p0 p5 p7 p3 : Prop)
theorem file84_69001 : ((((((p3 → p2) ∨ (p7 → p0)) ∧ ((p5 → p5) → (p1 ∨ p1))) ∧ (((False ∧ p0) → (p0 ∨ p4)) → False)) ∧ ((((p5 ∧ p4) ∧ (p0 ∨ p4)) → False) ∨ (((p7 ∨ p5) ∨ (False ∨ False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case inl assump_16 =>
            have assump_74 : ((False ∧ p0) → (p0 ∨ p4)) := by
              intro assump_22
              cases assump_22
              case intro assump_23 assump_24 =>
                apply False.elim assump_23
            let assump_21 := assump_5 assump_74
            apply False.elim assump_21
          case inr assump_17 =>
            have assump_75 : ((False ∧ p0) → (p0 ∨ p4)) := by
              intro assump_34
              cases assump_34
              case intro assump_35 assump_36 =>
                apply False.elim assump_35
            let assump_33 := assump_5 assump_75
            apply False.elim assump_33
        case inr assump_9 =>
          cases assump_3
          case inl assump_48 =>
            have assump_76 : ((False ∧ p0) → (p0 ∨ p4)) := by
              intro assump_54
              cases assump_54
              case intro assump_55 assump_56 =>
                apply False.elim assump_55
            let assump_53 := assump_5 assump_76
            apply False.elim assump_53
          case inr assump_49 =>
            have assump_77 : ((False ∧ p0) → (p0 ∨ p4)) := by
              intro assump_66
              cases assump_66
              case intro assump_67 assump_68 =>
                apply False.elim assump_67
            let assump_65 := assump_5 assump_77
            apply False.elim assump_65


variable (p3 p7 p1 p6 p2 p4 : Prop)
theorem file84_70893 : ((((((p3 → False) ∨ (p1 ∧ p3)) → ((False ∧ p7) → False)) ∨ (((p6 → True) ∨ (False → p2)) ∨ ((p3 → p2) → (p4 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p3 → False) ∨ (p1 ∧ p3)) → ((False ∧ p7) → False)) ∨ (((p6 → True) ∨ (False → p2)) ∨ ((p3 → p2) → (p4 ∧ p6)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p4 p1 p5 p3 p7 : Prop)
theorem file84_71458 : (((((False ∨ False) → False) → ((p3 → False) ∧ (p5 → False))) → (((p0 ∨ False) ∧ (p5 ∧ p0)) → False)) ∨ ((((p0 → True) → (p1 → False)) → ((p0 ∧ p3) ∨ (p7 → False))) ∧ (((p4 ∨ True) ∨ (p1 → p3)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        have assump_33 : ((False ∨ False) → False) := by
          intro assump_18
          cases assump_18
          case inl assump_19 =>
            apply False.elim assump_19
          case inr assump_20 =>
            apply False.elim assump_20
        let assump_17 := assump_1 assump_33
        let assump_25 := And.right assump_17
        have assump_34 : p5 := by
          exact assump_9
        let assump_27 := assump_25 assump_34
        apply False.elim assump_27
    case inr assump_6 =>
      apply False.elim assump_6


variable (p4 p6 p7 p0 p5 p3 p1 p2 : Prop)
theorem file84_72475 : (((((p0 → False) → (p6 → p1)) ∨ ((False ∧ p6) ∧ (p7 → p5))) → (((p3 → False) ∨ (p1 → True)) ∨ ((True ∧ True) ∧ (p3 → False)))) → ((((p5 ∧ p2) → (p2 ∨ True)) ∨ ((p3 ∧ p4) ∨ (p4 → False))) ∨ (((p0 ∨ p3) ∧ (p2 ∨ p2)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    exact assump_6


variable (p2 p4 p5 p0 p3 p6 p1 : Prop)
theorem file84_72920 : (((((p6 ∧ True) → (p6 → p2)) → False) ∧ (((True ∨ p4) → False) ∧ ((p1 → p0) ∨ (p5 → False)))) → ((((False ∨ p0) → False) → False) ∨ (((p4 → p3) ∧ (False ∧ p1)) ∨ ((p3 ∨ p6) ∨ (p0 ∧ p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        have assump_34 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_19 := assump_6 assump_34
        apply False.elim assump_19
      case inr assump_11 =>
        apply Or.inl
        intro assump_25
        have assump_35 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_30 := assump_6 assump_35
        apply False.elim assump_30


variable (p4 p3 p2 p7 p0 p1 p6 p5 : Prop)
theorem file84_73815 : (((((p1 ∨ p4) → (p6 ∨ p0)) ∨ ((p7 → True) ∧ (p7 → p6))) → (((p5 ∧ True) → False) ∧ ((p5 ∨ False) → (p3 ∧ p3)))) → ((((p2 → False) ∨ (p1 → p1)) → ((p2 → False) → (p7 ∨ p0))) → (((p5 ∧ p1) → (p3 ∨ p5)) ∨ ((p6 → False) → (True ∧ p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply Or.inr
    exact assump_8


variable (p1 p5 p4 p3 p0 : Prop)
theorem file84_74265 : ((((((p5 → False) → False) → ((False → False) ∨ (p4 → False))) ∨ (((p0 → False) ∧ (False ∧ p1)) ∨ ((p3 ∧ p3) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p5 → False) → False) → ((False → False) ∨ (p4 → False))) ∨ (((p0 → False) ∧ (False ∧ p1)) ∨ ((p3 ∧ p3) → (p0 → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p4 p1 p7 p2 p5 : Prop)
theorem file84_74810 : (((((p1 → p6) ∨ (p5 ∨ p6)) ∧ ((p5 ∧ p6) ∧ (p4 ∨ True))) ∧ (((False ∧ p2) ∧ (p7 ∨ p7)) ∧ ((p5 → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_11
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_26
            case inr assump_19 =>
              cases assump_3
              case intro assump_32 assump_33 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  cases assump_34
                  case intro assump_36 assump_37 =>
                    apply False.elim assump_36
      case inr assump_7 =>
        cases assump_7
        case inl assump_40 =>
          cases assump_5
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              cases assump_45
              case inl assump_52 =>
                cases assump_3
                case intro assump_56 assump_57 =>
                  cases assump_56
                  case intro assump_58 assump_59 =>
                    cases assump_58
                    case intro assump_60 assump_61 =>
                      apply False.elim assump_60
              case inr assump_53 =>
                cases assump_3
                case intro assump_66 assump_67 =>
                  cases assump_66
                  case intro assump_68 assump_69 =>
                    cases assump_68
                    case intro assump_70 assump_71 =>
                      apply False.elim assump_70
        case inr assump_41 =>
          cases assump_5
          case intro assump_76 assump_77 =>
            cases assump_76
            case intro assump_78 assump_79 =>
              cases assump_77
              case inl assump_84 =>
                cases assump_3
                case intro assump_88 assump_89 =>
                  cases assump_88
                  case intro assump_90 assump_91 =>
                    cases assump_90
                    case intro assump_92 assump_93 =>
                      apply False.elim assump_92
              case inr assump_85 =>
                cases assump_3
                case intro assump_98 assump_99 =>
                  cases assump_98
                  case intro assump_100 assump_101 =>
                    cases assump_100
                    case intro assump_102 assump_103 =>
                      apply False.elim assump_102


variable (p0 p1 p4 : Prop)
theorem file84_77805 : (((((p0 → False) ∧ (p4 ∧ False)) → ((False ∧ False) ∧ (p1 → p0))) → False) → False) := by
  intro assump_12
  have assump_53 : (((p0 → False) ∧ (p4 ∧ False)) → ((False ∧ False) ∧ (p1 → p0))) := by
    intro assump_16
    apply And.intro
    apply And.intro
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        apply False.elim assump_22
    cases assump_16
    case intro assump_27 assump_28 =>
      cases assump_28
      case intro assump_31 assump_32 =>
        apply False.elim assump_32
    intro assump_37
    cases assump_16
    case intro assump_40 assump_41 =>
      cases assump_41
      case intro assump_44 assump_45 =>
        apply False.elim assump_45
  let assump_15 := assump_12 assump_53
  apply False.elim assump_15


variable (p0 p7 p2 p4 p3 : Prop)
theorem file84_78672 : ((((((True → False) ∨ (p0 → False)) ∧ ((p4 ∨ False) ∧ (p3 → False))) → False) ∧ ((((p0 → p7) ∨ (p4 ∨ p2)) → ((p0 ∨ True) ∨ (p3 ∧ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p0 → p7) ∨ (p4 ∨ p2)) → ((p0 ∨ True) ∨ (p3 ∧ p7))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p3 p0 p4 p2 p7 p5 p6 p1 : Prop)
theorem file84_79511 : (((((True ∨ True) ∧ (p3 → p1)) ∧ ((p6 ∧ True) → False)) → (((p6 ∧ p2) ∨ (True → False)) → False)) ∨ ((((p7 ∧ p5) ∨ (p4 ∧ p7)) ∨ ((p3 ∨ p0) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            have assump_69 : (p6 ∧ True) := by
              apply And.intro
              exact assump_5
              apply True.intro
            let assump_23 := assump_12 assump_69
            apply False.elim assump_23
          case inr assump_16 =>
            have assump_70 : (p6 ∧ True) := by
              apply And.intro
              exact assump_5
              apply True.intro
            let assump_33 := assump_12 assump_70
            apply False.elim assump_33
  case inr assump_4 =>
    cases assump_1
    case intro assump_39 assump_40 =>
      cases assump_39
      case intro assump_41 assump_42 =>
        cases assump_41
        case inl assump_43 =>
          have assump_71 : True := by
            apply True.intro
          let assump_53 := assump_4 assump_71
          apply False.elim assump_53
        case inr assump_44 =>
          have assump_72 : True := by
            apply True.intro
          let assump_65 := assump_4 assump_72
          apply False.elim assump_65


variable (p6 p0 p5 p1 p7 p2 : Prop)
theorem file84_81073 : ((((((p1 ∧ p2) ∧ (False → False)) → ((False ∨ p6) ∧ (False → False))) → (((p7 → False) ∧ (p5 ∧ False)) → ((p0 → p7) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p1 ∧ p2) ∧ (False → False)) → ((False ∨ p6) ∧ (False → False))) → (((p7 → False) ∧ (p5 ∧ False)) → ((p0 → p7) → (p6 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        apply False.elim assump_18
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p3 p5 p2 p1 : Prop)
theorem file84_81754 : ((((((p5 ∧ p1) → (p3 ∧ p5)) → False) → (((p1 → False) → (p3 → p2)) → ((p3 ∨ False) → (p1 → p3)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p5 ∧ p1) → (p3 ∧ p5)) → False) → (((p1 → False) → (p3 → p2)) → ((p3 ∨ False) → (p1 → p3)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      exact assump_11
    case inr assump_12 =>
      apply False.elim assump_12
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p3 p7 p4 p2 p6 p0 p5 : Prop)
theorem file84_82344 : (((((p5 ∧ False) ∧ (p7 ∨ p5)) → ((p3 ∧ p6) ∧ (p2 → p0))) → False) → ((((p5 ∨ False) → (p6 ∧ p4)) → ((p3 ∨ p4) ∧ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_39 : (((p5 ∧ False) ∧ (p7 ∨ p5)) → ((p3 ∧ p6) ∧ (p2 → p0))) := by
    intro assump_8
    apply And.intro
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    cases assump_8
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_20
    intro assump_25
    cases assump_8
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        apply False.elim assump_31
  let assump_7 := assump_1 assump_39
  apply False.elim assump_7


variable (p2 p0 p7 p5 p4 p1 p6 : Prop)
theorem file84_83270 : ((((((p1 → False) ∨ (p1 → False)) → False) ∨ (((p0 → False) → (p1 → False)) → False)) ∧ ((((p2 → False) ∧ (p6 → p0)) ∧ ((True ∧ False) ∧ (p7 → True))) ∧ (((p4 ∧ p5) ∨ (p2 ∨ p4)) → ((True → False) ∨ (False ∨ False))))) → False) := by
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
            cases assump_11
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_21
    case inr assump_5 =>
      cases assump_3
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_31
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                apply False.elim assump_41


variable (p1 p3 p2 p7 p5 p6 p4 p0 : Prop)
theorem file84_84487 : ((((((p6 → p7) ∨ (p5 → False)) ∨ ((p5 → False) ∧ (p7 ∧ p5))) ∨ (((p2 ∧ p2) → False) → ((p3 ∧ p5) → (p5 ∧ p3)))) ∧ ((((p4 → p3) → (False → False)) ∨ ((p7 → p1) → (p5 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_66 : (((p4 → p3) → (False → False)) ∨ ((p7 → p1) → (p5 ∧ p0))) := by
            apply Or.inl
            intro assump_15
            intro assump_16
            apply False.elim assump_16
          let assump_14 := assump_3 assump_66
          apply False.elim assump_14
        case inr assump_9 =>
          have assump_67 : (((p4 → p3) → (False → False)) ∨ ((p7 → p1) → (p5 ∧ p0))) := by
            apply Or.inl
            intro assump_27
            intro assump_28
            apply False.elim assump_28
          let assump_26 := assump_3 assump_67
          apply False.elim assump_26
      case inr assump_7 =>
        cases assump_7
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            have assump_68 : (((p4 → p3) → (False → False)) ∨ ((p7 → p1) → (p5 ∧ p0))) := by
              apply Or.inl
              intro assump_47
              intro assump_48
              apply False.elim assump_48
            let assump_46 := assump_3 assump_68
            apply False.elim assump_46
    case inr assump_5 =>
      have assump_69 : (((p4 → p3) → (False → False)) ∨ ((p7 → p1) → (p5 ∧ p0))) := by
        apply Or.inl
        intro assump_59
        intro assump_60
        apply False.elim assump_60
      let assump_58 := assump_3 assump_69
      apply False.elim assump_58


variable (p7 p5 p2 p0 p6 : Prop)
theorem file84_86332 : (((((p2 ∧ p6) ∨ (p5 → True)) → False) → False) ∨ ((((p7 → False) → False) → ((p0 → False) → (p0 ∨ p6))) → False)) := by
  apply Or.inl
  intro assump_17
  have assump_25 : ((p2 ∧ p6) ∨ (p5 → True)) := by
    apply Or.inr
    intro assump_21
    apply True.intro
  let assump_20 := assump_17 assump_25
  apply False.elim assump_20


variable (p2 p3 p1 p4 p0 p5 p7 : Prop)
theorem file84_86725 : (((((p3 → False) ∨ (p3 ∨ True)) → False) ∧ (((p7 → p0) → False) → False)) → ((((False ∧ p0) ∨ (p7 ∨ p7)) ∧ ((p5 → True) ∨ (p3 → p1))) → (((p5 → False) ∨ (p4 ∧ p0)) → ((p2 → True) ∨ (True ∨ p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_11 =>
        cases assump_11
        case inl assump_16 =>
          cases assump_9
          case inl assump_20 =>
            cases assump_1
            case intro assump_24 assump_25 =>
              apply Or.inl
              intro assump_30
              apply True.intro
          case inr assump_21 =>
            cases assump_1
            case intro assump_33 assump_34 =>
              apply Or.inl
              intro assump_39
              apply True.intro
        case inr assump_17 =>
          cases assump_9
          case inl assump_42 =>
            cases assump_1
            case intro assump_46 assump_47 =>
              apply Or.inl
              intro assump_52
              apply True.intro
          case inr assump_43 =>
            cases assump_1
            case intro assump_55 assump_56 =>
              apply Or.inl
              intro assump_61
              apply True.intro
  case inr assump_5 =>
    cases assump_5
    case intro assump_62 assump_63 =>
      cases assump_2
      case intro assump_68 assump_69 =>
        cases assump_68
        case inl assump_70 =>
          cases assump_70
          case intro assump_72 assump_73 =>
            apply False.elim assump_72
        case inr assump_71 =>
          cases assump_71
          case inl assump_76 =>
            cases assump_69
            case inl assump_80 =>
              cases assump_1
              case intro assump_84 assump_85 =>
                apply Or.inl
                intro assump_90
                apply True.intro
            case inr assump_81 =>
              cases assump_1
              case intro assump_93 assump_94 =>
                apply Or.inl
                intro assump_99
                apply True.intro
          case inr assump_77 =>
            cases assump_69
            case inl assump_102 =>
              cases assump_1
              case intro assump_106 assump_107 =>
                apply Or.inl
                intro assump_112
                apply True.intro
            case inr assump_103 =>
              cases assump_1
              case intro assump_115 assump_116 =>
                apply Or.inl
                intro assump_121
                apply True.intro


variable (p4 p2 p0 p1 p6 : Prop)
theorem file84_89525 : (((((p1 → False) → (False → False)) → False) ∨ (((True → p4) → False) ∧ ((False → p4) → False))) → ((((p6 ∨ True) ∧ (p2 ∨ p0)) ∨ ((p6 → False) ∨ (True → p4))) → False)) := by
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
          cases assump_1
          case inl assump_15 =>
            have assump_181 : ((p1 → False) → (False → False)) := by
              intro assump_20
              intro assump_21
              apply False.elim assump_21
            let assump_19 := assump_15 assump_181
            apply False.elim assump_19
          case inr assump_16 =>
            cases assump_16
            case intro assump_27 assump_28 =>
              have assump_182 : (False → p4) := by
                intro assump_34
                apply False.elim assump_34
              let assump_33 := assump_28 assump_182
              apply False.elim assump_33
        case inr assump_12 =>
          cases assump_1
          case inl assump_42 =>
            have assump_183 : ((p1 → False) → (False → False)) := by
              intro assump_47
              intro assump_48
              apply False.elim assump_48
            let assump_46 := assump_42 assump_183
            apply False.elim assump_46
          case inr assump_43 =>
            cases assump_43
            case intro assump_54 assump_55 =>
              have assump_184 : (False → p4) := by
                intro assump_61
                apply False.elim assump_61
              let assump_60 := assump_55 assump_184
              apply False.elim assump_60
      case inr assump_8 =>
        cases assump_6
        case inl assump_69 =>
          cases assump_1
          case inl assump_73 =>
            have assump_185 : ((p1 → False) → (False → False)) := by
              intro assump_78
              intro assump_79
              apply False.elim assump_79
            let assump_77 := assump_73 assump_185
            apply False.elim assump_77
          case inr assump_74 =>
            cases assump_74
            case intro assump_85 assump_86 =>
              have assump_186 : (False → p4) := by
                intro assump_92
                apply False.elim assump_92
              let assump_91 := assump_86 assump_186
              apply False.elim assump_91
        case inr assump_70 =>
          cases assump_1
          case inl assump_100 =>
            have assump_187 : ((p1 → False) → (False → False)) := by
              intro assump_105
              intro assump_106
              apply False.elim assump_106
            let assump_104 := assump_100 assump_187
            apply False.elim assump_104
          case inr assump_101 =>
            cases assump_101
            case intro assump_112 assump_113 =>
              have assump_188 : (False → p4) := by
                intro assump_119
                apply False.elim assump_119
              let assump_118 := assump_113 assump_188
              apply False.elim assump_118
  case inr assump_4 =>
    cases assump_4
    case inl assump_125 =>
      cases assump_1
      case inl assump_129 =>
        have assump_189 : ((p1 → False) → (False → False)) := by
          intro assump_134
          intro assump_135
          apply False.elim assump_135
        let assump_133 := assump_129 assump_189
        apply False.elim assump_133
      case inr assump_130 =>
        cases assump_130
        case intro assump_141 assump_142 =>
          have assump_190 : (False → p4) := by
            intro assump_148
            apply False.elim assump_148
          let assump_147 := assump_142 assump_190
          apply False.elim assump_147
    case inr assump_126 =>
      cases assump_1
      case inl assump_156 =>
        have assump_191 : ((p1 → False) → (False → False)) := by
          intro assump_161
          intro assump_162
          apply False.elim assump_162
        let assump_160 := assump_156 assump_191
        apply False.elim assump_160
      case inr assump_157 =>
        cases assump_157
        case intro assump_168 assump_169 =>
          have assump_192 : (False → p4) := by
            intro assump_175
            apply False.elim assump_175
          let assump_174 := assump_169 assump_192
          apply False.elim assump_174


variable (p5 p6 p4 p0 p7 : Prop)
theorem file84_93989 : (((((p4 → False) → (p7 ∨ p6)) ∧ ((True ∨ p5) → False)) → False) ∨ ((((p4 → False) → False) → ((p0 ∧ p6) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p6 p3 p4 p2 p1 : Prop)
theorem file84_94409 : (((((True → False) ∨ (p1 ∧ p3)) ∧ ((p2 ∨ p1) → False)) → (((p4 → False) ∨ (p1 ∨ p1)) ∧ ((p1 ∧ p3) ∧ (p1 → True)))) ∨ ((((p4 → p6) → (False → False)) ∧ ((p3 ∨ p3) → (p4 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_10
      have assump_78 : True := by
        apply True.intro
      let assump_15 := assump_4 assump_78
      apply False.elim assump_15
    case inr assump_5 =>
      cases assump_5
      case intro assump_19 assump_20 =>
        apply Or.inl
        intro assump_27
        have assump_79 : (p2 ∨ p1) := by
          apply Or.inr
          exact assump_19
        let assump_31 := assump_3 assump_79
        apply False.elim assump_31
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_35 assump_36 =>
    cases assump_35
    case inl assump_37 =>
      have assump_80 : True := by
        apply True.intro
      let assump_44 := assump_37 assump_80
      apply False.elim assump_44
    case inr assump_38 =>
      cases assump_38
      case intro assump_48 assump_49 =>
        exact assump_48
  cases assump_1
  case intro assump_56 assump_57 =>
    cases assump_56
    case inl assump_58 =>
      have assump_81 : True := by
        apply True.intro
      let assump_65 := assump_58 assump_81
      apply False.elim assump_65
    case inr assump_59 =>
      cases assump_59
      case intro assump_69 assump_70 =>
        exact assump_70
  intro assump_77
  apply True.intro


variable (p5 p4 p0 p3 p7 p1 p6 : Prop)
theorem file84_96052 : ((((((p6 ∨ p4) ∨ (False → p6)) → ((p4 ∧ p7) → (True ∧ True))) → (((p0 → False) → False) ∧ ((p6 ∧ p7) ∧ (p3 ∨ False)))) ∧ ((((p6 → p1) → (False → False)) ∨ ((p5 ∨ p4) ∨ (p7 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p6 → p1) → (False → False)) ∨ ((p5 ∨ p4) ∨ (p7 → p4))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p5 p7 p1 p0 : Prop)
theorem file84_96628 : (((((p7 ∧ p5) ∧ (p0 ∨ p0)) → ((p5 → False) → (p0 → p1))) → False) → False) := by
  intro assump_14
  have assump_56 : (((p7 ∧ p5) ∧ (p0 ∨ p0)) → ((p5 → False) → (p0 → p1))) := by
    intro assump_18
    intro assump_19
    intro assump_20
    cases assump_18
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_26
        case inl assump_33 =>
          have assump_57 : p5 := by
            exact assump_28
          let assump_40 := assump_19 assump_57
          apply False.elim assump_40
        case inr assump_34 =>
          have assump_58 : p5 := by
            exact assump_28
          let assump_49 := assump_19 assump_58
          apply False.elim assump_49
  let assump_17 := assump_14 assump_56
  apply False.elim assump_17


variable (p4 p0 p7 p5 p2 p3 p1 : Prop)
theorem file84_97498 : ((((((p0 → p3) → (p2 → p2)) ∨ ((p7 ∨ p7) → False)) ∨ (((p0 ∧ p4) → False) → ((p1 → False) ∨ (p5 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 → p3) → (p2 → p2)) ∨ ((p7 ∨ p7) → False)) ∨ (((p0 ∧ p4) → False) → ((p1 → False) ∨ (p5 ∧ p1)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p0 p6 p3 p2 p7 : Prop)
theorem file84_97988 : ((((((p2 → False) → False) → False) → (((p6 → p7) → False) → ((p0 ∨ True) ∨ (p3 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → False) → False) → False) → (((p6 → p7) → False) → ((p0 ∨ True) ∨ (p3 ∧ p1)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p3 p0 p4 p6 p2 p5 : Prop)
theorem file84_98451 : (((((p5 ∨ p3) → False) → ((p4 → True) ∧ (False → True))) ∨ (((False → p1) ∨ (p0 → False)) → False)) ∨ ((((p6 ∧ True) ∨ (False ∨ p5)) → False) → (((p5 ∨ p2) → False) ∧ ((False ∧ False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply True.intro
  intro assump_3
  apply True.intro


variable (p4 p0 p7 p3 p1 p5 p2 p6 : Prop)
theorem file84_98856 : ((((((p4 ∨ p3) → (True ∨ p3)) → False) ∨ (((p0 ∧ p2) → (False ∧ p5)) → ((p2 ∧ False) ∧ (p4 ∧ p5)))) ∧ ((((p3 ∧ p7) ∧ (p3 → False)) ∧ ((p1 ∨ p6) ∧ (p1 ∨ p2))) ∧ (((p0 → True) ∨ (p5 ∨ False)) ∨ ((True ∧ p5) → False)))) → False) := by
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
              cases assump_11
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_23
                  case inl assump_28 =>
                    cases assump_9
                    case inl assump_32 =>
                      cases assump_32
                      case inl assump_34 =>
                        have assump_358 : p3 := by
                          exact assump_14
                        let assump_41 := assump_13 assump_358
                        apply False.elim assump_41
                      case inr assump_35 =>
                        cases assump_35
                        case inl assump_45 =>
                          have assump_359 : p3 := by
                            exact assump_14
                          let assump_52 := assump_13 assump_359
                          apply False.elim assump_52
                        case inr assump_46 =>
                          apply False.elim assump_46
                    case inr assump_33 =>
                      have assump_360 : p3 := by
                        exact assump_14
                      let assump_63 := assump_13 assump_360
                      apply False.elim assump_63
                  case inr assump_29 =>
                    cases assump_9
                    case inl assump_69 =>
                      cases assump_69
                      case inl assump_71 =>
                        have assump_361 : p3 := by
                          exact assump_14
                        let assump_78 := assump_13 assump_361
                        apply False.elim assump_78
                      case inr assump_72 =>
                        cases assump_72
                        case inl assump_82 =>
                          have assump_362 : p3 := by
                            exact assump_14
                          let assump_89 := assump_13 assump_362
                          apply False.elim assump_89
                        case inr assump_83 =>
                          apply False.elim assump_83
                    case inr assump_70 =>
                      have assump_363 : p3 := by
                        exact assump_14
                      let assump_100 := assump_13 assump_363
                      apply False.elim assump_100
                case inr assump_25 =>
                  cases assump_23
                  case inl assump_106 =>
                    cases assump_9
                    case inl assump_110 =>
                      cases assump_110
                      case inl assump_112 =>
                        have assump_364 : p3 := by
                          exact assump_14
                        let assump_119 := assump_13 assump_364
                        apply False.elim assump_119
                      case inr assump_113 =>
                        cases assump_113
                        case inl assump_123 =>
                          have assump_365 : p3 := by
                            exact assump_14
                          let assump_130 := assump_13 assump_365
                          apply False.elim assump_130
                        case inr assump_124 =>
                          apply False.elim assump_124
                    case inr assump_111 =>
                      have assump_366 : p3 := by
                        exact assump_14
                      let assump_141 := assump_13 assump_366
                      apply False.elim assump_141
                  case inr assump_107 =>
                    cases assump_9
                    case inl assump_147 =>
                      cases assump_147
                      case inl assump_149 =>
                        have assump_367 : p3 := by
                          exact assump_14
                        let assump_156 := assump_13 assump_367
                        apply False.elim assump_156
                      case inr assump_150 =>
                        cases assump_150
                        case inl assump_160 =>
                          have assump_368 : p3 := by
                            exact assump_14
                          let assump_167 := assump_13 assump_368
                          apply False.elim assump_167
                        case inr assump_161 =>
                          apply False.elim assump_161
                    case inr assump_148 =>
                      have assump_369 : p3 := by
                        exact assump_14
                      let assump_178 := assump_13 assump_369
                      apply False.elim assump_178
    case inr assump_5 =>
      cases assump_3
      case intro assump_184 assump_185 =>
        cases assump_184
        case intro assump_186 assump_187 =>
          cases assump_186
          case intro assump_188 assump_189 =>
            cases assump_188
            case intro assump_190 assump_191 =>
              cases assump_187
              case intro assump_198 assump_199 =>
                cases assump_198
                case inl assump_200 =>
                  cases assump_199
                  case inl assump_204 =>
                    cases assump_185
                    case inl assump_208 =>
                      cases assump_208
                      case inl assump_210 =>
                        have assump_370 : p3 := by
                          exact assump_190
                        let assump_217 := assump_189 assump_370
                        apply False.elim assump_217
                      case inr assump_211 =>
                        cases assump_211
                        case inl assump_221 =>
                          have assump_371 : p3 := by
                            exact assump_190
                          let assump_228 := assump_189 assump_371
                          apply False.elim assump_228
                        case inr assump_222 =>
                          apply False.elim assump_222
                    case inr assump_209 =>
                      have assump_372 : p3 := by
                        exact assump_190
                      let assump_239 := assump_189 assump_372
                      apply False.elim assump_239
                  case inr assump_205 =>
                    cases assump_185
                    case inl assump_245 =>
                      cases assump_245
                      case inl assump_247 =>
                        have assump_373 : p3 := by
                          exact assump_190
                        let assump_254 := assump_189 assump_373
                        apply False.elim assump_254
                      case inr assump_248 =>
                        cases assump_248
                        case inl assump_258 =>
                          have assump_374 : p3 := by
                            exact assump_190
                          let assump_265 := assump_189 assump_374
                          apply False.elim assump_265
                        case inr assump_259 =>
                          apply False.elim assump_259
                    case inr assump_246 =>
                      have assump_375 : p3 := by
                        exact assump_190
                      let assump_276 := assump_189 assump_375
                      apply False.elim assump_276
                case inr assump_201 =>
                  cases assump_199
                  case inl assump_282 =>
                    cases assump_185
                    case inl assump_286 =>
                      cases assump_286
                      case inl assump_288 =>
                        have assump_376 : p3 := by
                          exact assump_190
                        let assump_295 := assump_189 assump_376
                        apply False.elim assump_295
                      case inr assump_289 =>
                        cases assump_289
                        case inl assump_299 =>
                          have assump_377 : p3 := by
                            exact assump_190
                          let assump_306 := assump_189 assump_377
                          apply False.elim assump_306
                        case inr assump_300 =>
                          apply False.elim assump_300
                    case inr assump_287 =>
                      have assump_378 : p3 := by
                        exact assump_190
                      let assump_317 := assump_189 assump_378
                      apply False.elim assump_317
                  case inr assump_283 =>
                    cases assump_185
                    case inl assump_323 =>
                      cases assump_323
                      case inl assump_325 =>
                        have assump_379 : p3 := by
                          exact assump_190
                        let assump_332 := assump_189 assump_379
                        apply False.elim assump_332
                      case inr assump_326 =>
                        cases assump_326
                        case inl assump_336 =>
                          have assump_380 : p3 := by
                            exact assump_190
                          let assump_343 := assump_189 assump_380
                          apply False.elim assump_343
                        case inr assump_337 =>
                          apply False.elim assump_337
                    case inr assump_324 =>
                      have assump_381 : p3 := by
                        exact assump_190
                      let assump_354 := assump_189 assump_381
                      apply False.elim assump_354


variable (p1 p4 p3 p7 p0 p2 p6 : Prop)
theorem file84_109188 : ((((((p1 ∧ p1) ∧ (p1 ∧ False)) → ((p3 ∧ p6) ∨ (p7 → False))) ∨ (((p7 ∧ p1) → (True → False)) ∨ ((p1 → p2) ∧ (p2 ∨ p0)))) → ((((True → False) ∧ (True ∧ p3)) → ((p3 ∨ False) ∧ (p3 ∨ p4))) → (((p2 → False) → (p7 → True)) → False))) → False) := by
  intro assump_1
  have assump_48 : ((((p1 ∧ p1) ∧ (p1 ∧ False)) → ((p3 ∧ p6) ∨ (p7 → False))) ∨ (((p7 ∧ p1) → (True → False)) ∨ ((p1 → p2) ∧ (p2 ∨ p0)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_48
  have assump_49 : (((True → False) ∧ (True ∧ p3)) → ((p3 ∨ False) ∧ (p3 ∨ p4))) := by
    intro assump_21
    apply And.intro
    cases assump_21
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        apply Or.inl
        exact assump_27
    cases assump_21
    case intro assump_32 assump_33 =>
      cases assump_33
      case intro assump_36 assump_37 =>
        apply Or.inl
        exact assump_37
  let assump_20 := assump_4 assump_49
  have assump_50 : ((p2 → False) → (p7 → True)) := by
    intro assump_43
    intro assump_44
    apply True.intro
  let assump_42 := assump_20 assump_50
  apply False.elim assump_42


variable (p6 p7 p3 p1 p4 p2 : Prop)
theorem file84_110620 : ((((((p7 ∧ p6) ∧ (p2 → False)) ∨ ((p1 → False) ∧ (p3 → False))) → False) ∧ ((((p6 ∨ p7) → False) ∧ ((p1 → p4) ∧ (False ∧ p7))) ∨ (((p6 ∨ p3) ∨ (p3 → p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
    case inr assump_7 =>
      have assump_29 : ((p6 ∨ p3) ∨ (p3 → p3)) := by
        apply Or.inr
        intro assump_23
        exact assump_23
      let assump_22 := assump_7 assump_29
      apply False.elim assump_22


variable (p6 p3 p1 p5 p0 p2 p4 : Prop)
theorem file84_111430 : (((((p3 → True) ∧ (False ∧ p0)) ∨ ((p4 → False) → (p0 → False))) → (((True → p1) → (p5 ∧ p0)) → ((False → p2) → (False ∧ True)))) → ((((p6 → p2) ∨ (False ∧ p1)) → False) → (((p5 → False) → (p1 → False)) → ((p4 ∨ False) → (p4 ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inl
    exact assump_5
  case inr assump_6 =>
    apply False.elim assump_6


variable (p4 p3 p7 p0 : Prop)
theorem file84_111924 : ((((((p3 → False) → (True → p4)) ∧ ((p7 ∧ p4) ∧ (p4 → False))) ∧ (((p7 ∨ False) → (True ∨ True)) → False)) ∨ ((((p7 → False) ∧ (p0 → False)) → ((p3 → False) → (True ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_49 : ((p7 ∨ False) → (True ∨ True)) := by
              intro assump_23
              cases assump_23
              case inl assump_24 =>
                apply Or.inl
                apply True.intro
              case inr assump_25 =>
                apply False.elim assump_25
            let assump_22 := assump_5 assump_49
            apply False.elim assump_22
  case inr assump_3 =>
    have assump_50 : (((p7 → False) ∧ (p0 → False)) → ((p3 → False) → (True ∨ True))) := by
      intro assump_36
      intro assump_37
      cases assump_36
      case intro assump_40 assump_41 =>
        apply Or.inl
        apply True.intro
    let assump_35 := assump_3 assump_50
    apply False.elim assump_35


variable (p5 p3 p0 p7 p1 : Prop)
theorem file84_113215 : ((((((True ∧ p1) → (p7 ∧ p0)) ∨ ((True ∧ p3) ∨ (p5 → False))) → False) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → False) → False) → False) := by
      intro assump_9
      have assump_23 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p6 p3 p4 p5 p0 p1 p7 p2 : Prop)
theorem file84_113816 : (((((False ∧ p2) ∧ (p0 ∨ p4)) ∧ ((False ∧ p6) ∧ (p6 ∨ False))) → (((False ∧ p6) ∧ (p2 → True)) → ((True → p5) → (p1 ∨ p6)))) ∨ ((((p6 ∨ p4) ∨ (p0 ∨ False)) ∧ ((p7 → False) → False)) → (((p6 ∧ p2) ∨ (True → True)) → ((p0 ∧ p3) → (p1 → p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply False.elim assump_8


variable (p1 p2 p4 p3 p7 p0 p5 : Prop)
theorem file84_114331 : (((((p2 ∨ p5) ∧ (p0 → False)) ∨ ((p3 ∨ True) ∨ (p4 → True))) ∧ (((p7 → True) → (p7 ∧ False)) → ((p0 ∧ p7) → False))) ∨ ((((p0 → True) ∨ (p0 → False)) → ((p1 → p2) ∨ (True → p4))) ∨ (((p2 ∨ p2) → (p2 ∧ False)) → ((p3 → False) ∧ (True ∧ False))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inr
  apply Or.inl
  apply Or.inr
  apply True.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_18 : (p7 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_1 assump_18
    let assump_13 := And.right assump_11
    apply False.elim assump_13


variable (p3 p2 p5 p1 p6 p7 : Prop)
theorem file84_115021 : ((((((p3 → p3) ∨ (False ∨ p2)) ∨ ((True ∨ p6) ∧ (p1 → False))) ∧ (((p3 ∧ False) ∧ (False → p7)) ∨ ((False → False) ∨ (p5 ∧ False)))) → False) → False) := by
  intro assump_5
  have assump_18 : ((((p3 → p3) ∨ (False ∨ p2)) ∨ ((True ∨ p6) ∧ (p1 → False))) ∧ (((p3 ∧ False) ∧ (False → p7)) ∨ ((False → False) ∨ (p5 ∧ False)))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    intro assump_9
    exact assump_9
    apply Or.inr
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  let assump_8 := assump_5 assump_18
  apply False.elim assump_8


variable (p2 p7 p0 p6 p4 p5 p3 : Prop)
theorem file84_115656 : (((((p6 ∨ p2) ∨ (p0 ∧ p5)) ∨ ((p4 ∨ p5) ∧ (p5 ∨ False))) → False) → ((((p2 → p5) → False) → ((p5 → p7) → (p2 → True))) ∨ (((True → False) ∨ (p3 ∨ p0)) → ((p4 → p0) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  apply True.intro


variable (p0 p2 p4 : Prop)
theorem file84_115991 : ((((((p0 ∨ False) → (p0 ∨ p4)) → False) → (((p0 → False) ∨ (False ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p0 ∨ False) → (p0 ∨ p4)) → False) → (((p0 → False) ∨ (False ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_32 : ((p0 ∨ False) → (p0 ∨ p4)) := by
        intro assump_14
        cases assump_14
        case inl assump_15 =>
          apply Or.inl
          exact assump_15
        case inr assump_16 =>
          apply False.elim assump_16
      let assump_13 := assump_5 assump_32
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p6 p0 p7 p1 p5 : Prop)
theorem file84_116871 : ((((((False → p1) → False) → ((p5 → False) → (p6 → p1))) ∨ (((p5 ∨ p5) ∧ (p0 → p1)) ∧ ((p7 ∨ p1) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False → p1) → False) → ((p5 → False) → (p6 → p1))) ∨ (((p5 ∨ p5) ∧ (p0 → p1)) ∧ ((p7 ∨ p1) → (False → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_25 : (False → p1) := by
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_5 assump_25
    apply False.elim assump_14
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p4 p7 p2 p1 p5 : Prop)
theorem file84_117533 : ((((((True → True) → False) → False) → False) ∧ ((((p2 ∨ False) → False) ∨ ((p2 ∨ p7) → (p4 → p5))) ∨ (((p1 ∧ p7) → (p7 → p7)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        have assump_60 : (((True → True) → False) → False) := by
          intro assump_18
          have assump_61 : (True → True) := by
            intro assump_22
            apply True.intro
          let assump_21 := assump_18 assump_61
          apply False.elim assump_21
        let assump_17 := assump_6 assump_60
        apply False.elim assump_17
      case inr assump_13 =>
        have assump_62 : (((True → True) → False) → False) := by
          intro assump_33
          have assump_63 : (True → True) := by
            intro assump_37
            apply True.intro
          let assump_36 := assump_33 assump_63
          apply False.elim assump_36
        let assump_32 := assump_6 assump_62
        apply False.elim assump_32
    case inr assump_11 =>
      have assump_64 : ((p1 ∧ p7) → (p7 → p7)) := by
        intro assump_47
        intro assump_48
        cases assump_47
        case intro assump_51 assump_52 =>
          exact assump_52
      let assump_46 := assump_11 assump_64
      apply False.elim assump_46


variable (p3 p2 p1 p4 p5 : Prop)
theorem file84_118945 : (((((p5 ∨ False) ∧ (p1 → p5)) ∧ ((p4 → p5) ∧ (False → False))) → False) → ((((p5 → False) ∨ (p1 ∧ p2)) ∨ ((False → True) ∧ (p5 → p3))) ∧ (((False → p4) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_34 : (((p5 ∨ False) ∧ (p1 → p5)) ∧ ((p4 → p5) ∧ (False → False))) := by
    apply And.intro
    apply And.intro
    apply Or.inl
    exact assump_4
    intro assump_9
    exact assump_4
    apply And.intro
    intro assump_12
    exact assump_4
    intro assump_15
    apply False.elim assump_15
  let assump_8 := assump_1 assump_34
  apply False.elim assump_8
  intro assump_21
  have assump_35 : (False → p4) := by
    intro assump_28
    apply False.elim assump_28
  let assump_27 := assump_21 assump_35
  apply False.elim assump_27


variable (p3 p1 p0 p5 p2 p7 : Prop)
theorem file84_119815 : ((((((p5 ∨ p1) → (p0 ∨ p5)) ∧ ((p3 ∧ False) ∧ (p2 → False))) → (((p7 ∧ p1) → False) → ((p7 ∧ p5) ∨ (p5 → p2)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p5 ∨ p1) → (p0 ∨ p5)) ∧ ((p3 ∧ False) ∧ (p2 → False))) → (((p7 ∧ p1) → False) → ((p7 ∧ p5) ∨ (p5 → p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p3 p5 p1 p2 p6 : Prop)
theorem file84_120484 : ((((((p2 ∧ p6) ∨ (False ∧ p1)) → ((True ∧ p5) → False)) → (((p5 → p2) ∧ (p3 ∨ p3)) → ((False → False) ∨ (p3 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p2 ∧ p6) ∨ (False ∧ p1)) → ((True ∧ p5) → False)) → (((p5 → p2) ∧ (p3 ∨ p3)) → ((False → False) ∨ (p3 ∨ p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
      case inr assump_12 =>
        apply Or.inl
        intro assump_24
        apply False.elim assump_24
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p1 p4 p5 p7 p0 p6 : Prop)
theorem file84_121237 : (((((True → False) → (False ∧ False)) → False) ∧ (((p7 → False) ∨ (False ∨ p5)) ∧ ((False → False) → False))) → ((((p6 → p0) → (p0 → False)) → False) ∧ (((p1 ∧ p6) → (False ∨ p4)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        have assump_76 : (False → False) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_10 assump_76
        apply False.elim assump_17
      case inr assump_12 =>
        cases assump_12
        case inl assump_24 =>
          apply False.elim assump_24
        case inr assump_25 =>
          have assump_77 : (False → False) := by
            intro assump_33
            apply False.elim assump_33
          let assump_32 := assump_10 assump_77
          apply False.elim assump_32
  intro assump_39
  cases assump_1
  case intro assump_42 assump_43 =>
    cases assump_43
    case intro assump_46 assump_47 =>
      cases assump_46
      case inl assump_48 =>
        have assump_78 : (False → False) := by
          intro assump_55
          apply False.elim assump_55
        let assump_54 := assump_47 assump_78
        apply False.elim assump_54
      case inr assump_49 =>
        cases assump_49
        case inl assump_61 =>
          apply False.elim assump_61
        case inr assump_62 =>
          have assump_79 : (False → False) := by
            intro assump_70
            apply False.elim assump_70
          let assump_69 := assump_47 assump_79
          apply False.elim assump_69


variable (p7 p0 p5 p6 p2 : Prop)
theorem file84_122956 : (((((True → False) ∧ (p6 → False)) → ((p5 ∧ p2) → (p0 ∧ True))) ∧ (((p7 ∧ True) → False) ∧ ((False → p2) ∧ (p0 ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15


variable (p2 p5 p4 p6 p1 p7 : Prop)
theorem file84_123441 : ((((((False ∨ False) → (False → False)) → ((True ∨ p2) ∨ (p7 → p5))) ∨ (((p2 ∨ p4) → False) → ((p6 ∨ p5) → False))) → ((((p1 ∧ False) → False) ∨ ((p4 → False) ∧ (p1 → p1))) → False)) → False) := by
  intro assump_1
  have assump_19 : ((((False ∨ False) → (False → False)) → ((True ∨ p2) ∨ (p7 → p5))) ∨ (((p2 ∨ p4) → False) → ((p6 ∨ p5) → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_19
  have assump_20 : (((p1 ∧ False) → False) ∨ ((p4 → False) ∧ (p1 → p1))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_4 assump_20
  apply False.elim assump_8


variable (p4 p5 p6 p1 p0 p7 : Prop)
theorem file84_124253 : ((((((True → False) ∧ (p4 → p6)) ∧ ((p7 ∨ p0) → False)) → (((False → False) → (p5 → False)) ∨ ((p5 ∧ p1) ∧ (p6 → p1)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((True → False) ∧ (p4 → p6)) ∧ ((p7 ∨ p0) → False)) → (((False → False) → (p5 → False)) ∨ ((p5 ∧ p1) ∧ (p6 → p1)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_16
        intro assump_17
        have assump_34 : True := by
          apply True.intro
        let assump_26 := assump_8 assump_34
        apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p4 p6 p7 p3 p5 p0 p1 : Prop)
theorem file84_125029 : (((((False → False) → False) ∧ ((True → False) ∧ (p5 → p6))) → (((p7 → False) → (p4 → False)) ∨ ((p0 → False) ∨ (True → False)))) ∨ ((((True ∧ p1) ∧ (p3 ∧ True)) ∧ ((p4 ∨ p7) → (p1 ∨ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      intro assump_13
      have assump_25 : True := by
        apply True.intro
      let assump_21 := assump_6 assump_25
      apply False.elim assump_21


variable (p2 p7 p1 : Prop)
theorem file84_125620 : ((((((True ∨ True) ∨ (p7 → p1)) → ((True ∧ True) → False)) → (((p2 → False) → False) ∧ ((True ∨ p7) ∨ (False → False)))) → False) → False) := by
  intro assump_15
  have assump_35 : ((((True ∨ True) ∨ (p7 → p1)) → ((True ∧ True) → False)) → (((p2 → False) → False) ∧ ((True ∨ p7) ∨ (False → False)))) := by
    intro assump_19
    apply And.intro
    intro assump_20
    have assump_36 : ((True ∨ True) ∨ (p7 → p1)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_25 := assump_19 assump_36
    have assump_37 : (True ∧ True) := by
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_26 := assump_25 assump_37
    apply False.elim assump_26
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_18 := assump_15 assump_35
  apply False.elim assump_18


