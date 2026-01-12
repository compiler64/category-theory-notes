#import "@preview/theorion:0.4.1": *
#show: show-theorion

#show emph: it => {
  if text.style == "normal" {
    text(style: "italic", it.body)
  } else {
    text(style: "normal", it.body)
  }
}

#let of = $op(circle.small)$
#let dom = $op("dom")$
#let cod = $op("cod")$
#let cat(name) = $op(#text(font: "Libertinus Serif", style: "normal")[#name])$
#let Set = $cat("Set")$
#let Grp = $cat("Grp")$
#let Ring = $cat("Ring")$
#let Vect = $cat("Vect")$
#let Top = $cat("Top")$
