import numpy as np
from scipy.cluster.hierarchy import dendrogram, linkage, fcluster
from scipy.spatial.distance import pdist, squareform
import matplotlib.pyplot as plt
from ConfigFile import TH_d

def context_similarity(set1, set2):
    if (set1 == set2):
        return 1
    return len(set1&set2)/len(set1|set2)

def clust(data):
    dist_matrix = np.array([[1 - context_similarity(x, y) for y in data] for x in data])

    linked = linkage(squareform(dist_matrix), method='average')
    max_distance = linked[-1, 2]

    clusters = fcluster(linked, TH_d, criterion='distance')

    return clusters[0]

