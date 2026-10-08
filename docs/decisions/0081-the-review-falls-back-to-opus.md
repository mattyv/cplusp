# 0081: The review falls back to Opus

Date: 2026-10-08. Status: decided. Amends 0066 on who reviews. The user decided this in conversation.

## Decision

- The `reviewer` agent runs on Fable, decision 0066. When Fable is not available, for example when its credits run out, the same review runs on Opus. The brief, the checks and the rules stay the same.
- The commit of a green step names the model of its review when that model is not Fable.

## Why

A review that waits for one model stops the work. The review is the step that tries to break each contract. A second strong model can do that, and a review on Opus is better than no review.
