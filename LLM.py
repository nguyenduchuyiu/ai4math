import argparse
import os
import sys
import textwrap
from pathlib import Path
import torch
from transformers import AutoTokenizer, AutoModelForCausalLM
from transformers import TextIteratorStreamer


# MODEL_ID = "AI-MO/Kimina-Prover-Preview-Distill-7B"
MODEL_ID = "Goedel-LM/Goedel-Prover-V2-8B"


def load_model(model_id: str = MODEL_ID):
    """
    Load tokenizer/model with automatic GPU+CPU sharding (needs accelerate).
    If accelerate is missing, instruct how to install.
    """
    tokenizer = AutoTokenizer.from_pretrained(model_id, use_fast=False)
    dtype = torch.bfloat16 if torch.cuda.is_available() else torch.float32

    model = AutoModelForCausalLM.from_pretrained(
        model_id,
        dtype=dtype,
        device_map="cpu",  # spreads layers across available devices/CPU
    )

    return tokenizer, model


def generate_reply(prompt: str, max_new_tokens: int, temperature: float, top_p: float):
    tokenizer, model = load_model()

    inputs = tokenizer(prompt, return_tensors="pt")
    inputs = {k: v.to(model.device) for k, v in inputs.items()}

    streamer = TextIteratorStreamer(tokenizer, skip_prompt=True, skip_special_tokens=True)
    gen_kwargs = dict(
        **inputs,
        max_new_tokens=max_new_tokens,
        do_sample=temperature > 0,
        temperature=temperature,
        top_p=top_p,
        eos_token_id=tokenizer.eos_token_id,
        streamer=streamer,
    )

    # Launch generation in a background thread
    import threading

    thread = threading.Thread(target=model.generate, kwargs=gen_kwargs)
    thread.start()

    # Stream tokens to stdout
    output_chunks = []
    for token in streamer:
        sys.stdout.write(token)
        sys.stdout.flush()
        output_chunks.append(token)

    thread.join()
    return "".join(output_chunks)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--prompt",
        type=str, 
        default=textwrap.dedent(
            """
            <|im_start|>system
            You are an expert in mathematics and Lean 4.
            Given a Lean proof state, produce valid Lean 4 tactics to solve the current goal.
            <|im_end|>

            <|im_start|>user
            Solve the following Lean 4 proof state.
            lean4
            import Mathlib
            set_option maxHeartbeats 0
            open BigOperators Real Nat Topology Rat
            lemma aime_1983_p3_1_1
                (f : ℝ → ℝ)
                (h₀ : ∀ x : ℝ,
                    f x =
                    x ^ 2 + (18 * x + 30) - 2 * √(x ^ 2 + 18 * x + 45))
                (h₁ : Fintype (↑(f ⁻¹' {0}) : Type)) :
                ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by
                have h2 : ∀ x : ℝ, f x = 0 ↔ x = -9 + √61 ∨ x = -9 - √61 := by
                    intro x
                    constructor
                    · -- Assume f(x) = 0, prove x = -9 ± √61
                        intro hx
                        have hfx : f x = x ^ 2 + (18 * x + 30) - 2 * √(x ^ 2 + 18 * x + 45) := h₀ x
                        rw [hfx] at hx
                        have h_eq : x ^ 2 + (18 * x + 30) - 2 * √(x ^ 2 + 18 * x + 45) = 0 := hx
                        have h1 : 2 * √(x ^ 2 + 18 * x + 45) = x ^ 2 + 18 * x + 30 := by linarith
                        have h2 : x ^ 2 + 18 * x + 45 ≥ 0 := by
                            nlinarith [Real.sqrt_nonneg (x ^ 2 + 18 * x + 45)]
                        have h3 : √(x ^ 2 + 18 * x + 45) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 18 * x + 45)
                        have h4 : x ^ 2 + 18 * x + 30 ≥ 0 := by nlinarith
                        have h5 : x ^ 2 + 18 * x + 30 = 2 * √(x ^ 2 + 18 * x + 45) := by linarith
                        have h6 : (x ^ 2 + 18 * x + 30) ^ 2 = 4 * (x ^ 2 + 18 * x + 45) := by
                            have hsq : (2 * √(x ^ 2 + 18 * x + 45)) ^ 2 = 4 * (x ^ 2 + 18 * x + 45) := by
                                calc
                                    (2 * √(x ^ 2 + 18 * x + 45)) ^ 2 = 4 * (√(x ^ 2 + 18 * x + 45) ^ 2) := by ring
                                    _ = 4 * (x ^ 2 + 18 * x + 45) := by rw [Real.sq_sqrt h2]
                            rw [← h5] at hsq
                            nlinarith
                        have h7 : (x - (-9 + √61)) * (x - (-9 - √61)) = 0 := by
                            ring_nf
                            nlinarith [h6, Real.sq_sqrt (show 0 ≤ 61 by norm_num : (61 : ℝ) ≥ 0)]
                        cases' (mul_eq_zero.mp h7) with h8 h9
                        · left
            Continue the proof using Lean tactics.
            <|im_end|>

            <|im_start|>assistant

            """
        ).strip(),
        help="Text prompt to send to the model.",
    )
    parser.add_argument("--max-new-tokens", type=int, default=16384)
    parser.add_argument("--temperature", type=float, default=0.9)
    parser.add_argument("--top-p", type=float, default=0.95)
    args = parser.parse_args()

    print("\n=== Model reply (streaming) ===\n")
    generate_reply(
        args.prompt,
        max_new_tokens=args.max_new_tokens,
        temperature=args.temperature,
        top_p=args.top_p,
    )
    print()  # newline at end


if __name__ == "__main__":
    main()
