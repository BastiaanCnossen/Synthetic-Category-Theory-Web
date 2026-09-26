"""Temporary manuscript IDs that survive TeX4ht's punctuation normalization."""
import hashlib


def public_anchor(label):
    """Preserve published IDs; encode the rare TeX label with whitespace."""
    if any(c.isspace() for c in label):
        return 'sct-public-'+hashlib.sha256(label.encode('utf-8')).hexdigest()
    return label


def conversion_anchor(label):
    # Assembly restores the source label. Distinct labels such as "x y" and
    # "x_y" must not collapse to the same intermediate HTML ID.
    return 'sct-label-'+hashlib.sha256(label.encode('utf-8')).hexdigest()
