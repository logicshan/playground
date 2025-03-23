\chapter{Summary}

A table with the rules for different type formers of the languages defined in the previous chapters.
\\

\begin{tabular}{l l l l l l}
type formation & constructor               & destructor               & computation                          & uniqueness    &  \\\hline\hline
\verb$Bool$    & \verb$true$,              & \verb$ite$               & \verb$iteβ₁$,                        &               &  Chapter \ref{ch:precision} \\
               & \verb$false$              &                          & \verb$iteβ₂$                         &               &  \\\cline{1-5}
\verb$Nat$     & \verb$num$                & \verb$isZero$,           & \verb$isZeroβ₁$, \verb$isZeroβ₂$,    &               &  \\
               &                           & \verb$_+o_$              & \verb$+β$                            &               &  \\\hline
\verb$_⇒_$     & \verb$lam$                & \verb._$_.               & \verb$⇒β$                            & \verb$⇒η$     &  Chapter \ref{ch:STT} \\\hline
\verb$_×o_$    & \verb$_,o_$               & \verb$fst$, \verb$snd$   & \verb$×β₁$, \verb$×β₂$               & \verb$×η$     &  Chapter \ref{ch:Fin} \\\cline{1-5}
\verb$Unit$    & \verb$trivial$            &                          &                                      & \verb$Unitη$  &  \\\cline{1-5}
\verb$_+o_$    & \verb$inl$, \verb$inr$    & \verb$caseo$             & \verb$+β₁$, \verb$+β₂$               & \verb$+η$     &  \\\cline{1-5}
\verb$Empty$   &                           & \verb$absurd$            &                                      & \verb$Emptyη$ &  \\\hline
\verb$Nat$     & \verb$zeroo$,             & \verb$iteNat$            & \verb$Natβ₁$,                        &               &  Chapter \ref{ch:Ind} \\
               & \verb$suco$               &                          & \verb$Natβ₂$                         &               &  \\\cline{1-5}
\verb$List$    & \verb$nil$,               & \verb$iteList$           & \verb$Listβ₁$,                       &               &  \\
               & \verb$cons$               &                          & \verb$Listβ₂$                        &               &  \\\cline{1-5}
\verb$Tree$    & \verb$leaf$,              & \verb$iteTree$           & \verb$Treeβ₁$                        &               &  \\
               & \verb$node$               &                          & \verb$Treeβ₂$                        &               &  \\\hline
\verb$Stream$  & \verb$genStream$          & \verb$head$,             & \verb$Streamβ₁$,                     &               &  Chapter \ref{ch:Coind} \\
               &                           & \verb$tail$              & \verb$Streamβ₂$                      &               &  \\\cline{1-5}
\verb$Machine$ & \verb$genMachine$         & \verb$put$,              & \verb$Machineβ₁$,                    &               &  \\
               &                           & \verb$set$,              & \verb$Machineβ₂$,                    &               &  \\
               &                           & \verb$get$               & \verb$Machineβ₃$                     &               &  \\
\end{tabular}
